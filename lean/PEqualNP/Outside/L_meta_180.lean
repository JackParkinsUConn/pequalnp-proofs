import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_180

def ev {p : ℕ} (r : Bool ⊕ DMFormula p) (x : Fin p → Bool) : Bool :=
  match r with
  | Sum.inl c => c
  | Sum.inr ψ => ψ.eval x

def sz {p : ℕ} (r : Bool ⊕ DMFormula p) : ℕ :=
  match r with
  | Sum.inl _ => 0
  | Sum.inr ψ => ψ.leaves

def andR {p : ℕ} (r s : Bool ⊕ DMFormula p) : Bool ⊕ DMFormula p :=
  match r, s with
  | Sum.inl c, t => if c then t else Sum.inl false
  | Sum.inr a, Sum.inl c => if c then Sum.inr a else Sum.inl false
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.and a b)

def orR {p : ℕ} (r s : Bool ⊕ DMFormula p) : Bool ⊕ DMFormula p :=
  match r, s with
  | Sum.inl c, t => if c then Sum.inl true else t
  | Sum.inr a, Sum.inl c => if c then Sum.inl true else Sum.inr a
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.or a b)

theorem ev_andR {p : ℕ} (r s : Bool ⊕ DMFormula p) (x : Fin p → Bool) :
    ev (andR r s) x = (ev r x && ev s x) := by
  rcases r with c | a <;> rcases s with d | b
  · cases c <;> cases d <;> rfl
  · cases c <;> simp [andR, ev]
  · cases d <;> simp [andR, ev]
  · simp [andR, ev, DMFormula.eval]

theorem ev_orR {p : ℕ} (r s : Bool ⊕ DMFormula p) (x : Fin p → Bool) :
    ev (orR r s) x = (ev r x || ev s x) := by
  rcases r with c | a <;> rcases s with d | b
  · cases c <;> cases d <;> rfl
  · cases c <;> simp [orR, ev]
  · cases d <;> simp [orR, ev]
  · simp [orR, ev, DMFormula.eval]

theorem sz_andR {p : ℕ} (r s : Bool ⊕ DMFormula p) : sz (andR r s) ≤ sz r + sz s := by
  rcases r with c | a <;> rcases s with d | b
  · cases c <;> cases d <;> simp [andR, sz]
  · cases c <;> simp [andR, sz]
  · cases d <;> simp [andR, sz]
  · simp [andR, sz, DMFormula.leaves]

theorem sz_orR {p : ℕ} (r s : Bool ⊕ DMFormula p) : sz (orR r s) ≤ sz r + sz s := by
  rcases r with c | a <;> rcases s with d | b
  · cases c <;> cases d <;> simp [orR, sz]
  · cases c <;> simp [orR, sz]
  · cases d <;> simp [orR, sz]
  · simp [orR, sz, DMFormula.leaves]

def assign {m p : ℕ} (σ : Fin m → Fin p ⊕ Bool) (x : Fin p → Bool) (i : Fin m) : Bool :=
  match σ i with
  | Sum.inl j => x j
  | Sum.inr c => c

def free {m p : ℕ} (σ : Fin m → Fin p ⊕ Bool) : DMFormula m → ℕ
  | DMFormula.lit i _ => if (σ i).isLeft then 1 else 0
  | DMFormula.and φ ψ => free σ φ + free σ ψ
  | DMFormula.or φ ψ => free σ φ + free σ ψ

def restr {m p : ℕ} (σ : Fin m → Fin p ⊕ Bool) : DMFormula m → Bool ⊕ DMFormula p
  | DMFormula.lit i b =>
    match σ i with
    | Sum.inl j => Sum.inr (DMFormula.lit j b)
    | Sum.inr c => Sum.inl (if b then c else !c)
  | DMFormula.and φ ψ => andR (restr σ φ) (restr σ ψ)
  | DMFormula.or φ ψ => orR (restr σ φ) (restr σ ψ)

theorem restr_spec {m p : ℕ} (σ : Fin m → Fin p ⊕ Bool) (φ : DMFormula m) :
    (∀ x, ev (restr σ φ) x = φ.eval (assign σ x)) ∧ sz (restr σ φ) ≤ free σ φ := by
  induction φ with
  | lit i b =>
    constructor
    · intro x
      cases h : σ i with
      | inl j => simp [restr, ev, assign, h, DMFormula.eval]
      | inr c => simp [restr, ev, assign, h, DMFormula.eval]
    · cases h : σ i with
      | inl j => simp [restr, sz, free, h, DMFormula.leaves]
      | inr c => simp [restr, sz, free, h]
  | and φ ψ ihφ ihψ =>
    refine ⟨fun x => ?_, ?_⟩
    · simp only [restr, DMFormula.eval, ev_andR, ihφ.1, ihψ.1]
    · simp only [restr, free]
      exact le_trans (sz_andR _ _) (Nat.add_le_add ihφ.2 ihψ.2)
  | or φ ψ ihφ ihψ =>
    refine ⟨fun x => ?_, ?_⟩
    · simp only [restr, DMFormula.eval, ev_orR, ihφ.1, ihψ.1]
    · simp only [restr, free]
      exact le_trans (sz_orR _ _) (Nat.add_le_add ihφ.2 ihψ.2)

def σL {n k : ℕ} (y : Fin k → Bool) : Fin (n + k) → Fin n ⊕ Bool :=
  Fin.addCases (fun i => Sum.inl i) (fun j => Sum.inr (y j))

def σR {n k : ℕ} (x : Fin n → Bool) : Fin (n + k) → Fin k ⊕ Bool :=
  Fin.addCases (fun i => Sum.inr (x i)) (fun j => Sum.inl j)

theorem free_sum {n k : ℕ} (y : Fin k → Bool) (x0 : Fin n → Bool) (φ : DMFormula (n + k)) :
    free (σL y) φ + free (σR x0) φ = φ.leaves := by
  induction φ with
  | lit i b =>
    induction i using Fin.addCases with
    | left i => simp [free, σL, σR, DMFormula.leaves]
    | right j => simp [free, σL, σR, DMFormula.leaves]
  | and φ ψ ihφ ihψ =>
    simp only [free, DMFormula.leaves]
    omega
  | or φ ψ ihφ ihψ =>
    simp only [free, DMFormula.leaves]
    omega

def ren {m m' : ℕ} (e : Fin m → Fin m') : DMFormula m → DMFormula m'
  | DMFormula.lit i b => DMFormula.lit (e i) b
  | DMFormula.and φ ψ => DMFormula.and (ren e φ) (ren e ψ)
  | DMFormula.or φ ψ => DMFormula.or (ren e φ) (ren e ψ)

theorem ren_eval {m m' : ℕ} (e : Fin m → Fin m') (φ : DMFormula m) (z : Fin m' → Bool) :
    (ren e φ).eval z = φ.eval (fun i => z (e i)) := by
  induction φ with
  | lit i b => simp [ren, DMFormula.eval]
  | and φ ψ ihφ ihψ => simp [ren, DMFormula.eval, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [ren, DMFormula.eval, ihφ, ihψ]

theorem ren_leaves {m m' : ℕ} (e : Fin m → Fin m') (φ : DMFormula m) :
    (ren e φ).leaves = φ.leaves := by
  induction φ with
  | lit i b => simp [ren, DMFormula.leaves]
  | and φ ψ ihφ ihψ => simp [ren, DMFormula.leaves, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [ren, DMFormula.leaves, ihφ, ihψ]

end PEqualNP.Outside.L_meta_180

theorem PEqualNP.Outside.L_meta_180 : ∀ (n k : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin k → Bool) → Bool) (a b : ℕ), (∃ x : Fin n → Bool, f x = true) → (∃ x : Fin n → Bool, f x = false) → (∃ y : Fin k → Bool, g y = true) → (∃ y : Fin k → Bool, g y = false) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize n f r ↔ a ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize k g r ↔ b ≤ r) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasLeafSize (n + k) (fun z : Fin (n + k) → Bool => f (fun i : Fin n => z (Fin.castAdd k i)) || g (fun j : Fin k => z (Fin.natAdd n j))) s ↔ a + b ≤ s) := by
  intro n k f g a b ⟨xt, hxt⟩ ⟨xf, hxf⟩ ⟨yt, hyt⟩ ⟨yf, hyf⟩ hf hg s
  constructor
  · rintro ⟨φ, hl, he⟩
    have hL := PEqualNP.Outside.L_meta_180.restr_spec (PEqualNP.Outside.L_meta_180.σL (n := n) yf) φ
    have hR := PEqualNP.Outside.L_meta_180.restr_spec (PEqualNP.Outside.L_meta_180.σR (k := k) xf) φ
    have evL : ∀ x, PEqualNP.Outside.L_meta_180.ev
        (PEqualNP.Outside.L_meta_180.restr (PEqualNP.Outside.L_meta_180.σL (n := n) yf) φ) x = f x := by
      intro x
      rw [hL.1, he]
      simp [PEqualNP.Outside.L_meta_180.assign, PEqualNP.Outside.L_meta_180.σL, hyf]
    have evR : ∀ y, PEqualNP.Outside.L_meta_180.ev
        (PEqualNP.Outside.L_meta_180.restr (PEqualNP.Outside.L_meta_180.σR (k := k) xf) φ) y = g y := by
      intro y
      rw [hR.1, he]
      simp [PEqualNP.Outside.L_meta_180.assign, PEqualNP.Outside.L_meta_180.σR, hxf]
    have ha : a ≤ PEqualNP.Outside.L_meta_180.free (PEqualNP.Outside.L_meta_180.σL (n := n) yf) φ := by
      have h2 := hL.2
      rcases hr : PEqualNP.Outside.L_meta_180.restr (PEqualNP.Outside.L_meta_180.σL (n := n) yf) φ with c | ψ
      · exfalso
        have h1 := evL xt
        have h3 := evL xf
        rw [hr] at h1 h3
        simp only [PEqualNP.Outside.L_meta_180.ev] at h1 h3
        rw [hxt] at h1
        rw [hxf] at h3
        rw [h1] at h3
        exact Bool.noConfusion h3
      · rw [hr] at h2
        apply (hf _).mp
        refine ⟨ψ, h2, fun x => ?_⟩
        have h1 := evL x
        rw [hr] at h1
        exact h1
    have hb : b ≤ PEqualNP.Outside.L_meta_180.free (PEqualNP.Outside.L_meta_180.σR (k := k) xf) φ := by
      have h2 := hR.2
      rcases hr : PEqualNP.Outside.L_meta_180.restr (PEqualNP.Outside.L_meta_180.σR (k := k) xf) φ with c | ψ
      · exfalso
        have h1 := evR yt
        have h3 := evR yf
        rw [hr] at h1 h3
        simp only [PEqualNP.Outside.L_meta_180.ev] at h1 h3
        rw [hyt] at h1
        rw [hyf] at h3
        rw [h1] at h3
        exact Bool.noConfusion h3
      · rw [hr] at h2
        apply (hg _).mp
        refine ⟨ψ, h2, fun y => ?_⟩
        have h1 := evR y
        rw [hr] at h1
        exact h1
    have hsum := PEqualNP.Outside.L_meta_180.free_sum yf xf φ
    omega
  · intro hs
    obtain ⟨φf, hlf, hef⟩ := (hf a).mpr le_rfl
    obtain ⟨φg, hlg, heg⟩ := (hg b).mpr le_rfl
    refine ⟨DMFormula.or (PEqualNP.Outside.L_meta_180.ren (Fin.castAdd k) φf)
      (PEqualNP.Outside.L_meta_180.ren (Fin.natAdd n) φg), ?_, fun z => ?_⟩
    · simp only [DMFormula.leaves, PEqualNP.Outside.L_meta_180.ren_leaves]
      omega
    · simp only [DMFormula.eval, PEqualNP.Outside.L_meta_180.ren_eval, hef, heg]
