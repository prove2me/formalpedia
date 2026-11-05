-- Prove2me | solution 1 for ComputationalOTAudit.EntropicDuality.entropic_duality_and_scalings
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:48:39.693604+00:00
-- url     : https://prove2.me/submissions/83782358-2989-4820-b542-be9d2b425e58

import Mathlib
import Definitions.Def_ComputationalOTAudit_EntropicDuality_support_interface

set_option autoImplicit false
set_option linter.all false

namespace ED71

/-- One-dimensional concave bound: `x a - ε e^{x/ε} A ≤ ε log(a/A) a - ε a`. -/
lemma phi_le {ε a A x : ℝ} (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A) :
    x * a - ε * (Real.exp (x / ε) * A) ≤ ε * Real.log (a / A) * a - ε * a := by
  set L := Real.log (a / A) with hL
  set y := x / ε - L with hy
  have hexpL : Real.exp L = a / A := Real.exp_log (div_pos ha hA)
  have h1 : Real.exp (x / ε) * A = a * Real.exp y := by
    have : x / ε = y + L := by rw [hy]; ring
    rw [this, Real.exp_add, hexpL]; field_simp
  have hx : x = ε * (y + L) := by rw [hy]; field_simp; ring
  rw [h1, hx]
  have hk := mul_nonneg (mul_pos hε ha).le (sub_nonneg.2 (Real.add_one_le_exp y))
  nlinarith [hk]

lemma phi_eq {ε a A x : ℝ} (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A)
    (h : x * a - ε * (Real.exp (x / ε) * A) = ε * Real.log (a / A) * a - ε * a) :
    Real.exp (x / ε) * A = a := by
  set L := Real.log (a / A) with hL
  set y := x / ε - L with hy
  have hexpL : Real.exp L = a / A := Real.exp_log (div_pos ha hA)
  have h1 : Real.exp (x / ε) * A = a * Real.exp y := by
    have : x / ε = y + L := by rw [hy]; ring
    rw [this, Real.exp_add, hexpL]; field_simp
  have hx : x = ε * (y + L) := by rw [hy]; field_simp; ring
  rw [h1, hx] at h
  have hy0 : y = 0 := by
    by_contra hne
    have := Real.add_one_lt_exp hne
    have hpos := mul_pos (mul_pos hε ha) (sub_pos.2 this)
    nlinarith [hpos]
  rw [h1, hy0, Real.exp_zero, mul_one]

lemma phi_at {ε a A : ℝ} (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A) :
    (ε * Real.log (a / A)) * a - ε * (Real.exp (ε * Real.log (a / A) / ε) * A)
      = ε * Real.log (a / A) * a - ε * a := by
  have : ε * Real.log (a / A) / ε = Real.log (a / A) := by field_simp
  rw [this, Real.exp_log (div_pos ha hA)]
  field_simp

/-- Fenchel-Young defect `x log x - x - x y + e^y`. -/
noncomputable def psi (x y : ℝ) : ℝ := x * Real.log x - x - x * y + Real.exp y

lemma psi_nonneg {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : 0 ≤ psi x y := by
  unfold psi
  rcases hx.eq_or_lt with h | h
  · subst h; simp [Real.exp_pos y |>.le]
  · set t := Real.log x
    have hxt : Real.exp t = x := Real.exp_log h
    have hey : Real.exp y = x * Real.exp (y - t) := by
      rw [← hxt, ← Real.exp_add]; congr 1; ring
    rw [hey]
    have := mul_nonneg h.le (sub_nonneg.2 (Real.add_one_le_exp (y - t)))
    nlinarith [this]

lemma psi_eq_zero {x y : ℝ} (hx : 0 ≤ x) (h : psi x y = 0) : x = Real.exp y := by
  rcases hx.eq_or_lt with h0 | hx
  · subst h0
    unfold psi at h
    simp at h
  unfold psi at h
  set t := Real.log x
  have hxt : Real.exp t = x := Real.exp_log hx
  have hey : Real.exp y = x * Real.exp (y - t) := by
    rw [← hxt, ← Real.exp_add]; congr 1; ring
  rw [hey] at h
  have hyt : y - t = 0 := by
    by_contra hne
    have := Real.add_one_lt_exp hne
    have := mul_pos hx (sub_pos.2 this)
    nlinarith [this]
  rw [hey, hyt, Real.exp_zero, mul_one]

lemma psi_self (y : ℝ) : psi (Real.exp y) y = 0 := by
  unfold psi; rw [Real.log_exp]; ring

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Gibbs kernel on arbitrary finite index types. -/
noncomputable def gk (C : ι → κ → ℝ) (ε : ℝ) (i : ι) (j : κ) : ℝ := Real.exp (-C i j / ε)

/-- Entropic dual objective on arbitrary finite index types. -/
noncomputable def dualG (C : ι → κ → ℝ) (α : ι → ℝ) (β : κ → ℝ) (ε : ℝ)
    (f : ι → ℝ) (g : κ → ℝ) : ℝ :=
  (∑ i, f i * α i) + (∑ j, g j * β j) -
    ε * ∑ i, ∑ j, Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε)

/-- Entropic primal objective on arbitrary finite index types. -/
noncomputable def primalG (C : ι → κ → ℝ) (ε : ℝ) (R : ι → κ → ℝ) : ℝ :=
  (∑ i, ∑ j, C i j * R i j) - ε * ∑ i, ∑ j, (Real.negMulLog (R i j) + R i j)

/-- Couplings on arbitrary finite index types. -/
def cplG (α : ι → ℝ) (β : κ → ℝ) : Set (ι → κ → ℝ) :=
  {R | (∀ i j, 0 ≤ R i j) ∧ (∀ i, ∑ j, R i j = α i) ∧ (∀ j, ∑ i, R i j = β j)}

noncomputable def rowA (C : ι → κ → ℝ) (ε : ℝ) (g : κ → ℝ) (i : ι) : ℝ :=
  ∑ j, gk C ε i j * Real.exp (g j / ε)

noncomputable def colB (C : ι → κ → ℝ) (ε : ℝ) (f : ι → ℝ) (j : κ) : ℝ :=
  ∑ i, Real.exp (f i / ε) * gk C ε i j

lemma gk_pos (C : ι → κ → ℝ) (ε : ℝ) (i : ι) (j : κ) : 0 < gk C ε i j := Real.exp_pos _

lemma rowA_pos [Nonempty κ] (C : ι → κ → ℝ) (ε : ℝ) (g : κ → ℝ) (i : ι) :
    0 < rowA C ε g i := by
  unfold rowA
  exact Finset.sum_pos (fun j _ => mul_pos (gk_pos C ε i j) (Real.exp_pos _))
    Finset.univ_nonempty

lemma colB_pos [Nonempty ι] (C : ι → κ → ℝ) (ε : ℝ) (f : ι → ℝ) (j : κ) :
    0 < colB C ε f j := by
  unfold colB
  exact Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (gk_pos C ε i j))
    Finset.univ_nonempty

lemma dual_rows (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (ε : ℝ)
    (f : ι → ℝ) (g : κ → ℝ) :
    dualG C a b ε f g =
      (∑ i, (f i * a i - ε * (Real.exp (f i / ε) * rowA C ε g i))) + ∑ j, g j * b j := by
  unfold dualG rowA
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have : ∀ i, Real.exp (f i / ε) * ∑ j, gk C ε i j * Real.exp (g j / ε)
      = ∑ j, Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε) := by
    intro i; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [this]; ring

lemma dual_cols (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (ε : ℝ)
    (f : ι → ℝ) (g : κ → ℝ) :
    dualG C a b ε f g =
      (∑ j, (g j * b j - ε * (Real.exp (g j / ε) * colB C ε f j))) + ∑ i, f i * a i := by
  unfold dualG colB
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm (f := fun i j =>
    Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε))]
  have : ∀ j, Real.exp (g j / ε) * ∑ i, Real.exp (f i / ε) * gk C ε i j
      = ∑ i, Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε) := by
    intro j; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [this]; ring

noncomputable def updF (C : ι → κ → ℝ) (a : ι → ℝ) (ε : ℝ)
    (g : κ → ℝ) (i : ι) : ℝ := ε * Real.log (a i / rowA C ε g i)

noncomputable def updG (C : ι → κ → ℝ) (b : κ → ℝ) (ε : ℝ)
    (f : ι → ℝ) (j : κ) : ℝ := ε * Real.log (b j / colB C ε f j)

lemma dual_le_updF [Nonempty κ] (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (ha_pos : ∀ i, 0 < a i) (f : ι → ℝ) (g : κ → ℝ) :
    dualG C a b ε f g ≤ dualG C a b ε (updF C a ε g) g := by
  rw [dual_rows, dual_rows]
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) le_rfl
  unfold updF
  rw [phi_at hε (ha_pos i) (rowA_pos C ε g i)]
  exact phi_le hε (ha_pos i) (rowA_pos C ε g i)

lemma dual_le_updG [Nonempty ι] (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hb_pos : ∀ j, 0 < b j) (f : ι → ℝ) (g : κ → ℝ) :
    dualG C a b ε f g ≤ dualG C a b ε f (updG C b ε f) := by
  rw [dual_cols, dual_cols]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) le_rfl
  unfold updG
  rw [phi_at hε (hb_pos j) (colB_pos C ε f j)]
  exact phi_le hε (hb_pos j) (colB_pos C ε f j)

lemma dual_shift (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hsa : ∑ i, a i = 1) (hsb : ∑ j, b j = 1) (f : ι → ℝ) (g : κ → ℝ) (c : ℝ) :
    dualG C a b ε (fun i => f i + c) (fun j => g j - c) = dualG C a b ε f g := by
  unfold dualG
  have h1 : ∑ i, (f i + c) * a i = (∑ i, f i * a i) + c := by
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsa]; ring
  have h2 : ∑ j, (g j - c) * b j = (∑ j, g j * b j) - c := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsb]; ring
  have h3 : ∀ i j, Real.exp ((f i + c) / ε) * gk C ε i j * Real.exp ((g j - c) / ε)
      = Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε) := by
    intro i j
    have e1 : (f i + c) / ε = f i / ε + c / ε := by ring
    have e2 : (g j - c) / ε = g j / ε - c / ε := by ring
    rw [e1, e2, Real.exp_add, Real.exp_sub]
    have := Real.exp_pos (c / ε)
    field_simp
  rw [h1, h2]
  simp_rw [h3]
  ring

lemma scal_eq (C : ι → κ → ℝ) {ε : ℝ} (f : ι → ℝ) (g : κ → ℝ) (i : ι) (j : κ) :
    Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε)
      = Real.exp ((f i + g j - C i j) / ε) := by
  unfold gk; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma gap_eq (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (Q : ι → κ → ℝ) (hQ : Q ∈ cplG a b) (f : ι → ℝ) (g : κ → ℝ) :
    primalG C ε Q - dualG C a b ε f g
      = ∑ i, ∑ j, ε * psi (Q i j) ((f i + g j - C i j) / ε) := by
  obtain ⟨_, hrow, hcol⟩ := hQ
  have hfa : ∑ i, f i * a i = ∑ i, ∑ j, f i * Q i j := by
    simp_rw [← hrow, Finset.mul_sum]
  have hgb : ∑ j, g j * b j = ∑ i, ∑ j, g j * Q i j := by
    rw [Finset.sum_comm]; simp_rw [← hcol, Finset.mul_sum]
  have key : ∀ i j, C i j * Q i j - ε * (Real.negMulLog (Q i j) + Q i j)
      - (f i * Q i j + g j * Q i j)
      + ε * (Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε))
      = ε * psi (Q i j) ((f i + g j - C i j) / ε) := by
    intro i j
    rw [scal_eq]
    have hy : (f i + g j - C i j) / ε * ε = f i + g j - C i j := div_mul_cancel₀ _ hε.ne'
    unfold psi Real.negMulLog
    linear_combination (Q i j) * hy
  unfold primalG dualG
  rw [hfa, hgb]
  simp_rw [← key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_add]
  ring

lemma weak_dual (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (Q : ι → κ → ℝ) (hQ : Q ∈ cplG a b) (f : ι → ℝ) (g : κ → ℝ) :
    dualG C a b ε f g ≤ primalG C ε Q := by
  have h := gap_eq C a b hε Q hQ f g
  have : 0 ≤ ∑ i, ∑ j, ε * psi (Q i j) ((f i + g j - C i j) / ε) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg hε.le (psi_nonneg _ (hQ.1 i j))))
  linarith

/-- Equality in weak duality forces the Gibbs form. -/
lemma gap_zero_form (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (Q : ι → κ → ℝ) (hQ : Q ∈ cplG a b) (f : ι → ℝ) (g : κ → ℝ)
    (hle : primalG C ε Q ≤ dualG C a b ε f g) :
    ∀ i j, Q i j = Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε) := by
  have h := gap_eq C a b hε Q hQ f g
  have hnn : ∀ i j, 0 ≤ ε * psi (Q i j) ((f i + g j - C i j) / ε) :=
    fun i j => mul_nonneg hε.le (psi_nonneg _ (hQ.1 i j))
  have hz : ∑ i, ∑ j, ε * psi (Q i j) ((f i + g j - C i j) / ε) = 0 := by
    apply le_antisymm
    · rw [← h]; linarith
    · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))
  intro i j
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hnn i j))).1 hz i (Finset.mem_univ i)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 h2 j
    (Finset.mem_univ j)
  have h4 : psi (Q i j) ((f i + g j - C i j) / ε) = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hε.ne'
    · exact h
  rw [psi_eq_zero (hQ.1 i j) h4, scal_eq C f g i j]

/-- A coupling of Gibbs form closes the duality gap. -/
lemma gap_zero_of_form (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (Q : ι → κ → ℝ) (hQ : Q ∈ cplG a b) (f : ι → ℝ) (g : κ → ℝ)
    (hform : ∀ i j, Q i j = Real.exp (f i / ε) * gk C ε i j * Real.exp (g j / ε)) :
    primalG C ε Q = dualG C a b ε f g := by
  have h := gap_eq C a b hε Q hQ f g
  have h0 : ∀ i j, ε * psi (Q i j) ((f i + g j - C i j) / ε) = 0 := by
    intro i j
    rw [hform i j, scal_eq C f g i j, psi_self, mul_zero]
  simp_rw [h0, Finset.sum_const_zero] at h
  linarith

lemma log_bounds {ε L A M x : ℝ} (hε : 0 < ε) (hA : 0 < A) (ha : 0 < x)
    (hlo : Real.exp (-M / ε) ≤ A) (hhi : A ≤ Real.exp (M / ε)) (hL : L = ε * Real.log (x / A)) :
    ε * Real.log x - M ≤ L ∧ L ≤ ε * Real.log x + M := by
  have h1 : Real.log A ≤ M / ε := (Real.log_le_iff_le_exp hA).2 hhi
  have h2 : -M / ε ≤ Real.log A := (Real.le_log_iff_exp_le hA).2 hlo
  have h1' : Real.log A * ε ≤ M := (le_div_iff₀ hε).1 h1
  have h2' : -M ≤ Real.log A * ε := (div_le_iff₀ hε).1 h2
  rw [hL, Real.log_div ha.ne' hA.ne']
  constructor <;> nlinarith

lemma exp_div_bounds {ε L M x : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hlo : ε * Real.log x - M ≤ L) (hhi : L ≤ ε * Real.log x + M) :
    x * Real.exp (-M / ε) ≤ Real.exp (L / ε) ∧ Real.exp (L / ε) ≤ x * Real.exp (M / ε) := by
  have e1 : (ε * Real.log x + M) / ε = Real.log x + M / ε := by
    rw [add_div, mul_div_cancel_left₀ _ hε.ne']
  have e2 : (ε * Real.log x - M) / ε = Real.log x + -M / ε := by
    rw [sub_div, mul_div_cancel_left₀ _ hε.ne', neg_div]; ring
  have u : L / ε ≤ Real.log x + M / ε := by
    rw [← e1]; exact (div_le_div_iff_of_pos_right hε).2 hhi
  have l : Real.log x + -M / ε ≤ L / ε := by
    rw [← e2]; exact (div_le_div_iff_of_pos_right hε).2 hlo
  constructor
  · calc x * Real.exp (-M / ε) = Real.exp (Real.log x + -M / ε) := by
          rw [Real.exp_add, Real.exp_log hx]
      _ ≤ _ := Real.exp_le_exp.2 l
  · calc Real.exp (L / ε) ≤ Real.exp (Real.log x + M / ε) := Real.exp_le_exp.2 u
      _ = x * Real.exp (M / ε) := by rw [Real.exp_add, Real.exp_log hx]

/-- Sinkhorn scalings exist for positive marginals of equal unit mass. -/
theorem exists_scaling [Nonempty ι] [Nonempty κ] (C : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hsa : ∑ i, a i = 1) (hsb : ∑ j, b j = 1)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ j, 0 < b j) :
    ∃ f : ι → ℝ, ∃ g : κ → ℝ,
      (∀ i, Real.exp (f i / ε) * rowA C ε g i = a i) ∧
      (∀ j, Real.exp (g j / ε) * colB C ε f j = b j) := by
  set M : ℝ := ∑ i, ∑ j, |C i j| with hM
  have hCM : ∀ i j, |C i j| ≤ M := by
    intro i j
    calc |C i j| ≤ ∑ j', |C i j'| :=
          Finset.single_le_sum (f := fun j' => |C i j'|) (fun j' _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ M := Finset.single_le_sum (f := fun i => ∑ j, |C i j|)
            (fun i' _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  have hK : ∀ i j, Real.exp (-M / ε) ≤ gk C ε i j ∧ gk C ε i j ≤ Real.exp (M / ε) := by
    intro i j
    have h := abs_le.1 (hCM i j)
    unfold gk
    constructor
    · exact Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right hε).2 (by linarith))
    · exact Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right hε).2 (by linarith))
  have hrowB : ∀ g : κ → ℝ, ∑ j, Real.exp (g j / ε) = 1 → ∀ i,
      Real.exp (-M / ε) ≤ rowA C ε g i ∧ rowA C ε g i ≤ Real.exp (M / ε) := by
    intro g hg i
    unfold rowA
    constructor
    · calc Real.exp (-M / ε) = ∑ j, Real.exp (-M / ε) * Real.exp (g j / ε) := by
            rw [← Finset.mul_sum, hg, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (hK i j).1 (Real.exp_pos _).le)
    · calc ∑ j, gk C ε i j * Real.exp (g j / ε)
            ≤ ∑ j, Real.exp (M / ε) * Real.exp (g j / ε) := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (hK i j).2 (Real.exp_pos _).le)
        _ = Real.exp (M / ε) := by rw [← Finset.mul_sum, hg, mul_one]
  have hcolB : ∀ f : ι → ℝ,
      (∀ i, ε * Real.log (a i) - M ≤ f i ∧ f i ≤ ε * Real.log (a i) + M) → ∀ j,
      Real.exp (-(2 * M) / ε) ≤ colB C ε f j ∧ colB C ε f j ≤ Real.exp ((2 * M) / ε) := by
    intro f hf j
    have hE : ∀ i, a i * Real.exp (-M / ε) ≤ Real.exp (f i / ε) ∧
        Real.exp (f i / ε) ≤ a i * Real.exp (M / ε) :=
      fun i => exp_div_bounds hε (ha_pos i) (hf i).1 (hf i).2
    have e2 : Real.exp ((2 * M) / ε) = Real.exp (M / ε) * Real.exp (M / ε) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2' : Real.exp (-(2 * M) / ε) = Real.exp (-M / ε) * Real.exp (-M / ε) := by
      rw [← Real.exp_add]; congr 1; ring
    unfold colB
    constructor
    · calc Real.exp (-(2 * M) / ε)
            = ∑ i, a i * Real.exp (-M / ε) * Real.exp (-M / ε) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hsa, one_mul, e2']
        _ ≤ _ := Finset.sum_le_sum (fun i _ =>
            mul_le_mul (hE i).1 (hK i j).1 (Real.exp_pos _).le (Real.exp_pos _).le)
    · calc ∑ i, Real.exp (f i / ε) * gk C ε i j
            ≤ ∑ i, a i * Real.exp (M / ε) * Real.exp (M / ε) := Finset.sum_le_sum (fun i _ =>
            mul_le_mul (hE i).2 (hK i j).2 (gk_pos C ε i j).le
              (mul_pos (ha_pos i) (Real.exp_pos _)).le)
        _ = Real.exp ((2 * M) / ε) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hsa, one_mul, e2]
  set S : Set ((ι → ℝ) × (κ → ℝ)) :=
    Set.Icc (fun i => ε * Real.log (a i) - M) (fun i => ε * Real.log (a i) + M) ×ˢ
    Set.Icc (fun j => ε * Real.log (b j) - 2 * M) (fun j => ε * Real.log (b j) + 2 * M)
    with hS
  have chain : ∀ f g, ∃ q ∈ S, dualG C a b ε f g ≤ dualG C a b ε q.1 q.2 := by
    intro f g
    set T := ∑ j, Real.exp (g j / ε) with hT
    have hTpos : 0 < T :=
      Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
    set c := ε * Real.log T with hc
    set g' : κ → ℝ := fun j => g j - c with hg'
    have hsum' : ∑ j, Real.exp (g' j / ε) = 1 := by
      have : ∀ j, Real.exp (g' j / ε) = Real.exp (g j / ε) / T := by
        intro j
        have : g' j / ε = g j / ε - Real.log T := by
          rw [hg', hc]; field_simp
        rw [this, Real.exp_sub, Real.exp_log hTpos]
      simp_rw [this]
      rw [← Finset.sum_div, ← hT, div_self hTpos.ne']
    set f1 := updF C a ε g' with hf1
    set g1 := updG C b ε f1 with hg1
    have hf1b : ∀ i, ε * Real.log (a i) - M ≤ f1 i ∧ f1 i ≤ ε * Real.log (a i) + M := by
      intro i
      exact log_bounds hε (rowA_pos C ε g' i) (ha_pos i) (hrowB g' hsum' i).1
        (hrowB g' hsum' i).2 rfl
    have hg1b : ∀ j, ε * Real.log (b j) - 2 * M ≤ g1 j ∧ g1 j ≤ ε * Real.log (b j) + 2 * M := by
      intro j
      exact log_bounds (M := 2 * M) hε (colB_pos C ε f1 j) (hb_pos j) (hcolB f1 hf1b j).1
        (hcolB f1 hf1b j).2 rfl
    refine ⟨(f1, g1), ?_, ?_⟩
    · refine ⟨⟨fun i => (hf1b i).1, fun i => (hf1b i).2⟩,
        ⟨fun j => (hg1b j).1, fun j => (hg1b j).2⟩⟩
    · calc dualG C a b ε f g
          = dualG C a b ε (fun i => f i + c) (fun j => g j - c) :=
            (dual_shift C a b hsa hsb f g c).symm
        _ ≤ dualG C a b ε f1 g' := dual_le_updF C a b hε ha_pos _ _
        _ ≤ dualG C a b ε f1 g1 := dual_le_updG C a b hε hb_pos _ _
  have hScpt : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSne : S.Nonempty := by
    obtain ⟨q, hq, _⟩ := chain 0 0
    exact ⟨q, hq⟩
  have hcont : Continuous (fun q : (ι → ℝ) × (κ → ℝ) => dualG C a b ε q.1 q.2) := by
    unfold dualG gk
    fun_prop
  obtain ⟨q, _, hqmax⟩ := hScpt.exists_isMaxOn hSne hcont.continuousOn
  have hglob : ∀ f g, dualG C a b ε f g ≤ dualG C a b ε q.1 q.2 := by
    intro f g
    obtain ⟨q', hq'S, hle⟩ := chain f g
    exact hle.trans ((isMaxOn_iff.1 hqmax) q' hq'S)
  refine ⟨q.1, q.2, ?_, ?_⟩
  · have h1 := hglob (updF C a ε q.2) q.2
    rw [dual_rows, dual_rows] at h1
    have hup : ∀ i, updF C a ε q.2 i * a i - ε * (Real.exp (updF C a ε q.2 i / ε)
        * rowA C ε q.2 i) = ε * Real.log (a i / rowA C ε q.2 i) * a i - ε * a i :=
      fun i => phi_at hε (ha_pos i) (rowA_pos C ε q.2 i)
    simp_rw [hup] at h1
    have hz : ∑ i, ((ε * Real.log (a i / rowA C ε q.2 i) * a i - ε * a i) -
        (q.1 i * a i - ε * (Real.exp (q.1 i / ε) * rowA C ε q.2 i))) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun i _ =>
          sub_nonneg.2 (phi_le hε (ha_pos i) (rowA_pos C ε q.2 i)))
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
          sub_nonneg.2 (phi_le hε (ha_pos i) (rowA_pos C ε q.2 i)))] at hz
    intro i
    exact phi_eq hε (ha_pos i) (rowA_pos C ε q.2 i)
      (by linarith [hz i (Finset.mem_univ i)])
  · have h1 := hglob q.1 (updG C b ε q.1)
    rw [dual_cols, dual_cols] at h1
    have hup : ∀ j, updG C b ε q.1 j * b j - ε * (Real.exp (updG C b ε q.1 j / ε)
        * colB C ε q.1 j) = ε * Real.log (b j / colB C ε q.1 j) * b j - ε * b j :=
      fun j => phi_at hε (hb_pos j) (colB_pos C ε q.1 j)
    simp_rw [hup] at h1
    have hz : ∑ j, ((ε * Real.log (b j / colB C ε q.1 j) * b j - ε * b j) -
        (q.2 j * b j - ε * (Real.exp (q.2 j / ε) * colB C ε q.1 j))) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun j _ =>
          sub_nonneg.2 (phi_le hε (hb_pos j) (colB_pos C ε q.1 j)))
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          sub_nonneg.2 (phi_le hε (hb_pos j) (colB_pos C ε q.1 j)))] at hz
    intro j
    exact phi_eq hε (hb_pos j) (colB_pos C ε q.1 j)
      (by linarith [hz j (Finset.mem_univ j)])

end Generic

open ComputationalOTAudit.EntropicDuality

variable {n m : ℕ}

/-- Restriction of a matrix to the positive supports. -/
def rM (a : Fin n → ℝ) (b : Fin m → ℝ) (R : Matrix (Fin n) (Fin m) ℝ) :
    PositiveSupport a → PositiveSupport b → ℝ := fun i j => R i.val j.val

/-- Restriction of a histogram to its positive support. -/
def rA (a : Fin n → ℝ) : PositiveSupport a → ℝ := fun i => a i.val

lemma sum_supp (a : Fin n → ℝ) (h : Fin n → ℝ) (hz : ∀ i, ¬ 0 < a i → h i = 0) :
    ∑ i : PositiveSupport a, h i.val = ∑ i, h i := by
  have h1 := Finset.sum_subtype (F := positiveSupportFintype a) (p := fun i => 0 < a i)
    (Finset.univ.filter (fun i => 0 < a i)) (by simp) h
  rw [Finset.sum_filter_of_ne (fun i _ hne => by_contra fun hn => hne (hz i hn))] at h1
  exact h1.symm

lemma dsum_supp (a : Fin n → ℝ) (b : Fin m → ℝ) (F : Fin n → Fin m → ℝ)
    (hz : ∀ i j, (¬ 0 < a i ∨ ¬ 0 < b j) → F i j = 0) :
    ∑ i : PositiveSupport a, ∑ j : PositiveSupport b, F i.val j.val = ∑ i, ∑ j, F i j :=
  (Finset.sum_congr rfl (fun i _ => sum_supp b (fun j => F i.val j)
    (fun j hj => hz i.val j (Or.inr hj)))).trans
    (sum_supp a (fun i => ∑ j, F i j)
      (fun i hi => Finset.sum_eq_zero (fun j _ => hz i j (Or.inl hi))))

lemma nonpos_zero {a : Fin n → ℝ} (ha : a ∈ stdSimplex ℝ (Fin n)) (i : Fin n)
    (hi : ¬ 0 < a i) : a i = 0 := le_antisymm (not_lt.1 hi) (ha.1 i)

lemma supp_mass {a : Fin n → ℝ} (ha : a ∈ stdSimplex ℝ (Fin n)) :
    ∑ i : PositiveSupport a, rA a i = 1 := by
  have := sum_supp a a (fun i hi => nonpos_zero ha i hi)
  rw [ha.2] at this
  exact this

lemma supp_nonempty {a : Fin n → ℝ} (ha : a ∈ stdSimplex ℝ (Fin n)) :
    Nonempty (PositiveSupport a) := by
  by_contra h
  have hall : ∀ i, ¬ 0 < a i := fun i hi => h ⟨⟨i, hi⟩⟩
  have : ∑ i, a i = 0 := Finset.sum_eq_zero (fun i _ => nonpos_zero ha i (hall i))
  rw [ha.2] at this
  exact one_ne_zero this

lemma cpl_zero {a : Fin n → ℝ} {b : Fin m → ℝ} {R : Matrix (Fin n) (Fin m) ℝ}
    (hR : R ∈ CompOT.Assignment.couplings a b) (i : Fin n) (j : Fin m)
    (h : ¬ 0 < a i ∨ ¬ 0 < b j) : R i j = 0 := by
  obtain ⟨hnn, hrow, hcol⟩ := hR
  rcases h with h | h
  · have : R i j ≤ ∑ j', R i j' :=
      Finset.single_le_sum (f := fun j' => R i j') (fun j' _ => hnn i j') (Finset.mem_univ j)
    rw [hrow i] at this
    exact le_antisymm (this.trans (not_lt.1 h)) (hnn i j)
  · have : R i j ≤ ∑ i', R i' j :=
      Finset.single_le_sum (f := fun i' => R i' j) (fun i' _ => hnn i' j) (Finset.mem_univ i)
    rw [hcol j] at this
    exact le_antisymm (this.trans (not_lt.1 h)) (hnn i j)

lemma cpl_restrict {a : Fin n → ℝ} {b : Fin m → ℝ} {R : Matrix (Fin n) (Fin m) ℝ}
    (hR : R ∈ CompOT.Assignment.couplings a b) : rM a b R ∈ cplG (rA a) (rA b) := by
  refine ⟨fun i j => hR.1 i.val j.val, fun i => ?_, fun j => ?_⟩
  · have := sum_supp b (fun j => R i.val j) (fun j hj => cpl_zero hR i.val j (Or.inr hj))
    rw [hR.2.1 i.val] at this
    exact this
  · have := sum_supp a (fun i => R i j.val) (fun i hi => cpl_zero hR i j.val (Or.inl hi))
    rw [hR.2.2 j.val] at this
    exact this

lemma cpl_extend {a : Fin n → ℝ} {b : Fin m → ℝ} (ha : a ∈ stdSimplex ℝ (Fin n))
    (hb : b ∈ stdSimplex ℝ (Fin m)) {R : Matrix (Fin n) (Fin m) ℝ}
    (hnn : ∀ i j, 0 ≤ R i j) (hz : ∀ i j, (¬ 0 < a i ∨ ¬ 0 < b j) → R i j = 0)
    (hr : rM a b R ∈ cplG (rA a) (rA b)) : R ∈ CompOT.Assignment.couplings a b := by
  refine ⟨hnn, fun i => ?_, fun j => ?_⟩
  · by_cases hi : 0 < a i
    · rw [← sum_supp b (fun j => R i j) (fun j hj => hz i j (Or.inr hj))]
      exact hr.2.1 ⟨i, hi⟩
    · rw [nonpos_zero ha i hi]
      exact Finset.sum_eq_zero (fun j _ => hz i j (Or.inl hi))
  · by_cases hj : 0 < b j
    · rw [← sum_supp a (fun i => R i j) (fun i hi => hz i j (Or.inl hi))]
      exact hr.2.2 ⟨j, hj⟩
    · rw [nonpos_zero hb j hj]
      exact Finset.sum_eq_zero (fun i _ => hz i j (Or.inr hj))

lemma ent_restrict (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} (ε : ℝ)
    {R : Matrix (Fin n) (Fin m) ℝ} (hR : R ∈ CompOT.Assignment.couplings a b) :
    CompOT.EntropicLimit.entObjective C ε R = primalG (rM a b C) ε (rM a b R) := by
  have e1 : (∑ i : PositiveSupport a, ∑ j : PositiveSupport b, C i.val j.val * R i.val j.val)
      = ∑ i, ∑ j, C i j * R i j :=
    dsum_supp a b (fun i j => C i j * R i j) (fun i j h => by simp [cpl_zero hR i j h])
  have e2 : (∑ i : PositiveSupport a, ∑ j : PositiveSupport b,
      (Real.negMulLog (R i.val j.val) + R i.val j.val))
      = ∑ i, ∑ j, (Real.negMulLog (R i j) + R i j) :=
    dsum_supp a b (fun i j => Real.negMulLog (R i j) + R i j)
      (fun i j h => by simp [cpl_zero hR i j h])
  show (∑ i, ∑ j, C i j * R i j) - ε * ∑ i, ∑ j, (Real.negMulLog (R i j) + R i j) = _
  rw [← e1, ← e2]
  rfl

lemma se_val (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) (i : PositiveSupport a) :
    SupportExp a ε f i.val = Real.exp (f i / ε) := by
  unfold SupportExp
  rw [dif_pos i.prop]
  rfl

lemma se_zero (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) (i : Fin n)
    (hi : ¬ 0 < a i) : SupportExp a ε f i = 0 := by
  unfold SupportExp
  rw [dif_neg hi]

lemma se_nonneg (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) (i : Fin n) :
    0 ≤ SupportExp a ε f i := by
  unfold SupportExp
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma scaled_zero (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ) (i : Fin n) (j : Fin m)
    (h : ¬ 0 < a i ∨ ¬ 0 < b j) :
    ScaledCoupling C ε (SupportExp a ε f) (SupportExp b ε g) i j = 0 := by
  unfold ScaledCoupling
  rcases h with h | h
  · rw [se_zero a ε f i h]; ring
  · rw [se_zero b ε g j h]; ring

lemma scaled_restrict (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ) :
    ∀ i j, rM a b (ScaledCoupling C ε (SupportExp a ε f) (SupportExp b ε g)) i j
      = Real.exp (f i / ε) * gk (rM a b C) ε i j * Real.exp (g j / ε) := by
  intro i j
  show SupportExp a ε f i.val * CompOT.EntropicDual.gibbs C ε i.val j.val *
    SupportExp b ε g j.val = _
  rw [se_val, se_val]
  rfl

lemma scaled_nonneg (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) {u : Fin n → ℝ} {v : Fin m → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) (i : Fin n) (j : Fin m) :
    0 ≤ ScaledCoupling C ε u v i j :=
  mul_nonneg (mul_nonneg (hu i) (Real.exp_pos _).le) (hv j)

lemma sdo_eq (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ) :
    SupportDualObjective C a b ε f g = dualG (rM a b C) (rA a) (rA b) ε f g := rfl

/-- Weak duality, support form. -/
lemma weak_supp (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) {R : Matrix (Fin n) (Fin m) ℝ} (hR : R ∈ CompOT.Assignment.couplings a b)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ) :
    SupportDualObjective C a b ε f g ≤ CompOT.EntropicLimit.entObjective C ε R := by
  rw [ent_restrict C ε hR, sdo_eq]
  exact weak_dual _ _ _ hε _ (cpl_restrict hR) f g

/-- Weak duality, full form. -/
lemma weak_full (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) {R : Matrix (Fin n) (Fin m) ℝ} (hR : R ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    CompOT.EntropicDual.dualObjEnt C a b ε f g ≤ CompOT.EntropicLimit.entObjective C ε R :=
  weak_dual C a b hε R hR f g

/-- Support equality case. -/
lemma eq_supp (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) {R : Matrix (Fin n) (Fin m) ℝ} (hR : R ∈ CompOT.Assignment.couplings a b)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ)
    (hle : CompOT.EntropicLimit.entObjective C ε R ≤ SupportDualObjective C a b ε f g) :
    R = ScaledCoupling C ε (SupportExp a ε f) (SupportExp b ε g) := by
  rw [ent_restrict C ε hR, sdo_eq] at hle
  have hform := gap_zero_form _ _ _ hε _ (cpl_restrict hR) f g hle
  funext i j
  by_cases hi : 0 < a i
  · by_cases hj : 0 < b j
    · have h1 := hform ⟨i, hi⟩ ⟨j, hj⟩
      have h2 := scaled_restrict C a b ε f g ⟨i, hi⟩ ⟨j, hj⟩
      exact h1.trans h2.symm
    · rw [cpl_zero hR i j (Or.inr hj), scaled_zero C a b ε f g i j (Or.inr hj)]
  · rw [cpl_zero hR i j (Or.inl hi), scaled_zero C a b ε f g i j (Or.inl hi)]

/-- Support zero-gap case. -/
lemma zero_supp (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ)
    (hR : ScaledCoupling C ε (SupportExp a ε f) (SupportExp b ε g)
      ∈ CompOT.Assignment.couplings a b) :
    CompOT.EntropicLimit.entObjective C ε
      (ScaledCoupling C ε (SupportExp a ε f) (SupportExp b ε g))
      = SupportDualObjective C a b ε f g := by
  rw [ent_restrict C ε hR, sdo_eq]
  exact gap_zero_of_form _ _ _ hε _ (cpl_restrict hR) f g (scaled_restrict C a b ε f g)

/-- Full equality case. -/
lemma eq_full (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) {R : Matrix (Fin n) (Fin m) ℝ} (hR : R ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hle : CompOT.EntropicLimit.entObjective C ε R ≤ CompOT.EntropicDual.dualObjEnt C a b ε f g) :
    R = ScaledCoupling C ε (FullExp ε f) (FullExp ε g) := by
  have hform := gap_zero_form C a b hε R hR f g hle
  funext i j
  exact hform i j

/-- Full zero-gap case. -/
lemma zero_full (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hR : ScaledCoupling C ε (FullExp ε f) (FullExp ε g) ∈ CompOT.Assignment.couplings a b) :
    CompOT.EntropicLimit.entObjective C ε (ScaledCoupling C ε (FullExp ε f) (FullExp ε g))
      = CompOT.EntropicDual.dualObjEnt C a b ε f g :=
  gap_zero_of_form C a b hε _ hR f g (fun _ _ => rfl)

/-- Positivity pattern of any nonnegative scaling whose matrix is a coupling. -/
lemma pos_pattern (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} (ε : ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    {u : Fin n → ℝ} {v : Fin m → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hR : ScaledCoupling C ε u v ∈ CompOT.Assignment.couplings a b) :
    (∀ i, 0 < u i ↔ 0 < a i) ∧ (∀ j, 0 < v j ↔ 0 < b j) := by
  have hK : ∀ i j, 0 < CompOT.EntropicDual.gibbs C ε i j := fun _ _ => Real.exp_pos _
  have hrow := hR.2.1
  have hcol := hR.2.2
  have hS : ∀ i j, ScaledCoupling C ε u v i j = u i * CompOT.EntropicDual.gibbs C ε i j * v j :=
    fun _ _ => rfl
  refine ⟨fun i => ⟨fun hui => ?_, fun hai => ?_⟩, fun j => ⟨fun hvj => ?_, fun hbj => ?_⟩⟩
  · by_contra hai
    have hz : ∀ j, v j = 0 := by
      intro j
      have h0 := cpl_zero hR i j (Or.inl hai)
      rw [hS] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (mul_pos hui (hK i j)).ne'
      · exact h
    have hb0 : ∀ j, b j = 0 := by
      intro j
      rw [← hcol j]
      exact Finset.sum_eq_zero (fun i' _ => by rw [hS, hz j, mul_zero])
    have : ∑ j, b j = 0 := Finset.sum_eq_zero (fun j _ => hb0 j)
    rw [hb.2] at this
    exact one_ne_zero this
  · by_contra hui
    have hu0 : u i = 0 := le_antisymm (not_lt.1 hui) (hu i)
    have : ∑ j, ScaledCoupling C ε u v i j = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hS, hu0, zero_mul, zero_mul])
    rw [hrow i] at this
    exact hai.ne' this
  · by_contra hbj
    have hz : ∀ i, u i = 0 := by
      intro i
      have h0 := cpl_zero hR i j (Or.inr hbj)
      rw [hS] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact h'
        · exact absurd h' (hK i j).ne'
      · exact absurd h hvj.ne'
    have ha0 : ∀ i, a i = 0 := by
      intro i
      rw [← hrow i]
      exact Finset.sum_eq_zero (fun j' _ => by rw [hS, hz i, zero_mul, zero_mul])
    have : ∑ i, a i = 0 := Finset.sum_eq_zero (fun i _ => ha0 i)
    rw [ha.2] at this
    exact one_ne_zero this
  · by_contra hvj
    have hv0 : v j = 0 := le_antisymm (not_lt.1 hvj) (hv j)
    have : ∑ i, ScaledCoupling C ε u v i j = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hS, hv0, mul_zero])
    rw [hcol j] at this
    exact hbj.ne' this

lemma se_sl {a : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε) {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hpos : ∀ i, 0 < u i ↔ 0 < a i) : SupportExp a ε (SupportLog a ε u) = u := by
  funext i
  unfold SupportExp SupportLog
  split_ifs with hi
  · have hui := (hpos i).2 hi
    rw [mul_div_cancel_left₀ _ hε.ne', Real.exp_log hui]
  · exact (le_antisymm (not_lt.1 (fun h => hi ((hpos i).1 h))) (hu i)).symm

lemma fe_fl {ε : ℝ} (hε : 0 < ε) {u : Fin n → ℝ} (hu : ∀ i, 0 < u i) :
    FullExp ε (FullLog ε u) = u := by
  funext i
  unfold FullExp FullLog
  rw [mul_div_cancel_left₀ _ hε.ne', Real.exp_log (hu i)]

/-- Indicator of the zero bins. -/
noncomputable def cInd (a : Fin n → ℝ) (i : Fin n) : ℝ := if 0 < a i then 0 else 1

/-- Support scaling perturbed by `δ` on the zero bins. -/
noncomputable def Ud (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) (δ : ℝ) (i : Fin n) : ℝ :=
  SupportExp a ε f i + δ * cInd a i

lemma Ud_pos (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (i : Fin n) : 0 < Ud a ε f δ i := by
  unfold Ud cInd
  by_cases hi : 0 < a i
  · rw [if_pos hi, mul_zero, add_zero]
    unfold SupportExp; rw [dif_pos hi]; exact Real.exp_pos _
  · rw [if_neg hi, mul_one, se_zero a ε f i hi, zero_add]; exact hδ

lemma Ud_val (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) (δ : ℝ)
    (i : PositiveSupport a) : Ud a ε f δ i.val = Real.exp (f i / ε) := by
  unfold Ud cInd
  rw [if_pos i.prop, mul_zero, add_zero, se_val]

lemma Ud_zero (a : Fin n → ℝ) (ε : ℝ) (f : PositiveSupport a → ℝ) (i : Fin n) :
    Ud a ε f 0 i = SupportExp a ε f i := by
  unfold Ud; rw [zero_mul, add_zero]

/-- The full dual supremum equals the support dual value of a Sinkhorn pair. -/
lemma sup_full (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f0 : PositiveSupport a → ℝ) (g0 : PositiveSupport b → ℝ)
    (hP : ScaledCoupling C ε (SupportExp a ε f0) (SupportExp b ε g0)
      ∈ CompOT.Assignment.couplings a b) :
    sSup (FullDualValues C a b ε) = SupportDualObjective C a b ε f0 g0 := by
  have hup : ∀ y ∈ FullDualValues C a b ε, y ≤ SupportDualObjective C a b ε f0 g0 := by
    rintro _ ⟨fg, rfl⟩
    rw [← zero_supp C hε f0 g0 hP]
    exact weak_full C hε hP _ _
  have hne : (FullDualValues C a b ε).Nonempty := ⟨_, ⟨(0, 0), rfl⟩⟩
  have hbdd : BddAbove (FullDualValues C a b ε) := ⟨_, hup⟩
  apply le_antisymm (csSup_le hne hup)
  let Φ : ℝ → ℝ := fun δ => (∑ i : PositiveSupport a, f0 i * a i.val) +
    (∑ j : PositiveSupport b, g0 j * b j.val) -
    ε * ∑ i, ∑ j, Ud a ε f0 δ i * CompOT.EntropicDual.gibbs C ε i j * Ud b ε g0 δ j
  have hΦc : Continuous Φ := by
    unfold Φ Ud
    fun_prop
  have hΦ0 : Φ 0 = SupportDualObjective C a b ε f0 g0 := by
    show (∑ i : PositiveSupport a, f0 i * a i.val) +
      (∑ j : PositiveSupport b, g0 j * b j.val) -
      ε * ∑ i, ∑ j, Ud a ε f0 0 i * CompOT.EntropicDual.gibbs C ε i j * Ud b ε g0 0 j = _
    simp only [Ud_zero]
    have e := dsum_supp a b
      (fun i j => SupportExp a ε f0 i * CompOT.EntropicDual.gibbs C ε i j * SupportExp b ε g0 j)
      (fun i j h => scaled_zero C a b ε f0 g0 i j h)
    unfold SupportDualObjective
    rw [← e]
    simp only [se_val]
  have hΦeq : ∀ δ, 0 < δ → CompOT.EntropicDual.dualObjEnt C a b ε
      (fun i => ε * Real.log (Ud a ε f0 δ i)) (fun j => ε * Real.log (Ud b ε g0 δ j)) = Φ δ := by
    intro δ hδ
    have hxU : ∀ i, Real.exp (ε * Real.log (Ud a ε f0 δ i) / ε) = Ud a ε f0 δ i := by
      intro i; rw [mul_div_cancel_left₀ _ hε.ne', Real.exp_log (Ud_pos a ε f0 hδ i)]
    have hxV : ∀ j, Real.exp (ε * Real.log (Ud b ε g0 δ j) / ε) = Ud b ε g0 δ j := by
      intro j; rw [mul_div_cancel_left₀ _ hε.ne', Real.exp_log (Ud_pos b ε g0 hδ j)]
    have h1 : ∑ i, ε * Real.log (Ud a ε f0 δ i) * a i = ∑ i : PositiveSupport a, f0 i * a i.val :=
      ((sum_supp a (fun i => ε * Real.log (Ud a ε f0 δ i) * a i)
        (fun i hi => by rw [nonpos_zero ha i hi, mul_zero])).symm).trans
        (Finset.sum_congr rfl (fun i _ => by
          rw [Ud_val, Real.log_exp, mul_div_cancel₀ _ hε.ne']))
    have h2 : ∑ j, ε * Real.log (Ud b ε g0 δ j) * b j = ∑ j : PositiveSupport b, g0 j * b j.val :=
      ((sum_supp b (fun j => ε * Real.log (Ud b ε g0 δ j) * b j)
        (fun j hj => by rw [nonpos_zero hb j hj, mul_zero])).symm).trans
        (Finset.sum_congr rfl (fun j _ => by
          rw [Ud_val, Real.log_exp, mul_div_cancel₀ _ hε.ne']))
    show (∑ i, ε * Real.log (Ud a ε f0 δ i) * a i) + (∑ j, ε * Real.log (Ud b ε g0 δ j) * b j) -
      ε * ∑ i, ∑ j, Real.exp (ε * Real.log (Ud a ε f0 δ i) / ε) *
        CompOT.EntropicDual.gibbs C ε i j * Real.exp (ε * Real.log (Ud b ε g0 δ j) / ε) = Φ δ
    rw [h1, h2]
    simp only [hxU, hxV]
    rfl
  have hlim : Filter.Tendsto Φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (Φ 0)) :=
    (hΦc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), Φ δ ≤ sSup (FullDualValues C a b ε) :=
    eventually_nhdsWithin_of_forall (fun δ hδ => by
      rw [← hΦeq δ hδ]
      exact le_csSup hbdd ⟨(_, _), rfl⟩)
  have := le_of_tendsto hlim hev
  rw [hΦ0] at this
  exact this

lemma cpl_of_foc (C : Matrix (Fin n) (Fin m) ℝ) {a : Fin n → ℝ} {b : Fin m → ℝ} {ε : ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f0 : PositiveSupport a → ℝ) (g0 : PositiveSupport b → ℝ)
    (hrow : ∀ i, Real.exp (f0 i / ε) * rowA (rM a b C) ε g0 i = rA a i)
    (hcol : ∀ j, Real.exp (g0 j / ε) * colB (rM a b C) ε f0 j = rA b j) :
    ScaledCoupling C ε (SupportExp a ε f0) (SupportExp b ε g0)
      ∈ CompOT.Assignment.couplings a b := by
  refine cpl_extend ha hb (scaled_nonneg C ε (se_nonneg a ε f0) (se_nonneg b ε g0))
    (scaled_zero C a b ε f0 g0) ⟨fun i j => scaled_nonneg C ε (se_nonneg a ε f0)
      (se_nonneg b ε g0) _ _, fun i => ?_, fun j => ?_⟩
  · rw [← hrow i]; unfold rowA; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [scaled_restrict]; ring)
  · rw [← hcol j]; unfold colB; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [scaled_restrict]; ring)

lemma fe_nonneg (ε : ℝ) (f : Fin n → ℝ) (i : Fin n) : 0 ≤ FullExp ε f i :=
  (Real.exp_pos _).le

lemma fe_pos (ε : ℝ) (f : Fin n → ℝ) (i : Fin n) : 0 < FullExp ε f i :=
  Real.exp_pos _

theorem main {n m : ℕ}
    (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (CompOT.Assignment.couplings a b).Nonempty ∧
    (PrimalValues C a b ε).Nonempty ∧ BddBelow (PrimalValues C a b ε) ∧
    (FullDualValues C a b ε).Nonempty ∧ BddAbove (FullDualValues C a b ε) ∧
    Nonempty (PositiveSupport a) ∧ Nonempty (PositiveSupport b) ∧
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      CompOT.EntropicLimit.IsEntropicOptimal C a b ε P ∧
      (∀ R, CompOT.EntropicLimit.IsEntropicOptimal C a b ε R → R = P) ∧
      CompOT.EntropicLimit.entObjective C ε P = PrimalValue C a b ε ∧
      PrimalValue C a b ε = sSup (FullDualValues C a b ε) ∧
      (∃ f : PositiveSupport a → ℝ, ∃ g : PositiveSupport b → ℝ,
        IsSupportDualMaximizer C a b ε f g ∧
        SupportDualObjective C a b ε f g = PrimalValue C a b ε) ∧
      (∀ (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ),
        IsSupportDualMaximizer C a b ε f g →
          SupportDualObjective C a b ε f g = PrimalValue C a b ε ∧
          RepresentsCoupling C ε P (SupportExp a ε f) (SupportExp b ε g)) ∧
      (∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
        (∀ i, 0 < u i ↔ 0 < a i) ∧ (∀ j, 0 < v j ↔ 0 < b j) ∧
        IsSupportDualMaximizer C a b ε (SupportLog a ε u) (SupportLog b ε v) ∧
        SupportExp a ε (SupportLog a ε u) = u ∧
        SupportExp b ε (SupportLog b ε v) = v) ∧
      (∀ (u : Fin n → ℝ) (v : Fin m → ℝ), IsFeasibleScaling C a b ε u v →
        ScaledCoupling C ε u v = P ∧
        CompOT.EntropicLimit.IsEntropicOptimal C a b ε (ScaledCoupling C ε u v)) ∧
      ((∃ f : Fin n → ℝ, ∃ g : Fin m → ℝ, IsFullDualMaximizer C a b ε f g) ↔
        FullSupport a ∧ FullSupport b) ∧
      (∀ (f : Fin n → ℝ) (g : Fin m → ℝ), IsFullDualMaximizer C a b ε f g →
        CompOT.EntropicDual.dualObjEnt C a b ε f g = PrimalValue C a b ε ∧
        RepresentsCoupling C ε P (FullExp ε f) (FullExp ε g)) ∧
      (FullSupport a ∧ FullSupport b →
        ∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
          (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
          IsFullDualMaximizer C a b ε (FullLog ε u) (FullLog ε v) ∧
          FullExp ε (FullLog ε u) = u ∧ FullExp ε (FullLog ε v) = v) := by
  have _hn := hn
  have _hm := hm
  have hsa := supp_mass ha
  have hsb := supp_mass hb
  have hIa := supp_nonempty ha
  have hIb := supp_nonempty hb
  obtain ⟨f0, g0, hrow0, hcol0⟩ := exists_scaling (rM a b C) (rA a) (rA b) ε hε hsa hsb
    (fun i => i.prop) (fun j => j.prop)
  have hP0 := cpl_of_foc C ha hb f0 g0 hrow0 hcol0
  obtain ⟨P, hPdef⟩ : ∃ P, P = ScaledCoupling C ε (SupportExp a ε f0) (SupportExp b ε g0) :=
    ⟨_, rfl⟩
  have hP : P ∈ CompOT.Assignment.couplings a b := hPdef ▸ hP0
  have hFP : CompOT.EntropicLimit.entObjective C ε P = SupportDualObjective C a b ε f0 g0 := by
    rw [hPdef]; exact zero_supp C hε f0 g0 hP0
  have hopt : ∀ Q ∈ CompOT.Assignment.couplings a b,
      CompOT.EntropicLimit.entObjective C ε P ≤ CompOT.EntropicLimit.entObjective C ε Q := by
    intro Q hQ; rw [hFP]; exact weak_supp C hε hQ f0 g0
  have huniq : ∀ R, CompOT.EntropicLimit.IsEntropicOptimal C a b ε R → R = P := by
    intro R hR
    rw [hPdef]
    exact eq_supp C hε hR.1 f0 g0 (hFP ▸ hR.2 P hP)
  have hPV : PrimalValue C a b ε = CompOT.EntropicLimit.entObjective C ε P := by
    unfold PrimalValue
    refine IsLeast.csInf_eq ⟨⟨⟨P, hP⟩, rfl⟩, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact hopt Q.1 Q.2
  have hsup : sSup (FullDualValues C a b ε) = CompOT.EntropicLimit.entObjective C ε P := by
    rw [hFP]; exact sup_full C hε ha hb f0 g0 hP0
  have hmax0 : IsSupportDualMaximizer C a b ε f0 g0 := by
    intro f' g'; rw [← hFP]; exact weak_supp C hε hP f' g'
  -- full-support scalings
  have hK : FullSupport a ∧ FullSupport b →
      ∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
        (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
        IsFullDualMaximizer C a b ε (FullLog ε u) (FullLog ε v) ∧
        FullExp ε (FullLog ε u) = u ∧ FullExp ε (FullLog ε v) = v := by
    rintro ⟨hfa, hfb⟩ u v ⟨hu, hv, hPuv⟩
    have hR : ScaledCoupling C ε u v ∈ CompOT.Assignment.couplings a b := hPuv ▸ hP
    have pos := pos_pattern C ε ha hb hu hv hR
    have hup : ∀ i, 0 < u i := fun i => (pos.1 i).2 (hfa i)
    have hvp : ∀ j, 0 < v j := fun j => (pos.2 j).2 (hfb j)
    have e1 := fe_fl hε hup
    have e2 := fe_fl hε hvp
    have hR' : ScaledCoupling C ε (FullExp ε (FullLog ε u)) (FullExp ε (FullLog ε v))
        ∈ CompOT.Assignment.couplings a b := by rw [e1, e2]; exact hR
    have hz := zero_full C hε (FullLog ε u) (FullLog ε v) hR'
    rw [e1, e2, ← hPuv] at hz
    refine ⟨hup, hvp, fun f' g' => ?_, e1, e2⟩
    rw [← hz]
    exact weak_full C hε hP f' g'
  -- facts about any full maximizer
  have hJ : ∀ (f : Fin n → ℝ) (g : Fin m → ℝ), IsFullDualMaximizer C a b ε f g →
      CompOT.EntropicDual.dualObjEnt C a b ε f g = PrimalValue C a b ε ∧
      RepresentsCoupling C ε P (FullExp ε f) (FullExp ε g) := by
    intro f g hmax
    have hgr : sSup (FullDualValues C a b ε) = CompOT.EntropicDual.dualObjEnt C a b ε f g := by
      refine IsGreatest.csSup_eq ⟨⟨(f, g), rfl⟩, ?_⟩
      rintro _ ⟨fg, rfl⟩
      exact hmax fg.1 fg.2
    have hval : CompOT.EntropicDual.dualObjEnt C a b ε f g = PrimalValue C a b ε := by
      rw [← hgr, hsup, hPV]
    refine ⟨hval, fe_nonneg ε f, fe_nonneg ε g, ?_⟩
    exact eq_full C hε hP f g (by rw [hval, hPV])
  refine ⟨⟨P, hP⟩, ⟨_, ⟨⟨P, hP⟩, rfl⟩⟩, ⟨CompOT.EntropicLimit.entObjective C ε P, ?_⟩,
    ⟨_, ⟨(0, 0), rfl⟩⟩, ⟨CompOT.EntropicLimit.entObjective C ε P, ?_⟩, hIa, hIb, P, ⟨hP, hopt⟩,
    huniq, hPV.symm, hPV.trans hsup.symm, ⟨f0, g0, hmax0, (hPV.trans hFP).symm⟩, ?_, ?_, ?_, ?_,
    hJ, hK⟩
  · rintro _ ⟨Q, rfl⟩
    exact hopt Q.1 Q.2
  · rintro _ ⟨fg, rfl⟩
    exact weak_full C hε hP _ _
  · -- every support maximizer
    intro f g hmax
    have hval : SupportDualObjective C a b ε f g = PrimalValue C a b ε := by
      apply le_antisymm
      · rw [hPV]; exact weak_supp C hε hP f g
      · rw [hPV, hFP]; exact hmax f0 g0
    refine ⟨hval, se_nonneg a ε f, se_nonneg b ε g, ?_⟩
    exact eq_supp C hε hP f g (by rw [hval, hPV])
  · -- every representation
    rintro u v ⟨hu, hv, hPuv⟩
    have hR : ScaledCoupling C ε u v ∈ CompOT.Assignment.couplings a b := hPuv ▸ hP
    have pos := pos_pattern C ε ha hb hu hv hR
    have e1 := se_sl (a := a) hε hu pos.1
    have e2 := se_sl (a := b) hε hv pos.2
    have hR' : ScaledCoupling C ε (SupportExp a ε (SupportLog a ε u))
        (SupportExp b ε (SupportLog b ε v)) ∈ CompOT.Assignment.couplings a b := by
      rw [e1, e2]; exact hR
    have hz := zero_supp C hε (SupportLog a ε u) (SupportLog b ε v) hR'
    rw [e1, e2, ← hPuv] at hz
    refine ⟨pos.1, pos.2, fun f' g' => ?_, e1, e2⟩
    rw [← hz]
    exact weak_supp C hε hP f' g'
  · -- every feasible scaling
    rintro u v ⟨hu, hv, hR⟩
    have pos := pos_pattern C ε ha hb hu hv hR
    have e1 := se_sl (a := a) hε hu pos.1
    have e2 := se_sl (a := b) hε hv pos.2
    have hR' : ScaledCoupling C ε (SupportExp a ε (SupportLog a ε u))
        (SupportExp b ε (SupportLog b ε v)) ∈ CompOT.Assignment.couplings a b := by
      rw [e1, e2]; exact hR
    have hz := zero_supp C hε (SupportLog a ε u) (SupportLog b ε v) hR'
    rw [e1, e2] at hz
    have hopt' : CompOT.EntropicLimit.IsEntropicOptimal C a b ε (ScaledCoupling C ε u v) := by
      refine ⟨hR, fun Q hQ => ?_⟩
      rw [hz]
      exact (weak_supp C hε hP _ _).trans (hopt Q hQ)
    exact ⟨huniq _ hopt', hopt'⟩
  · -- full maximizers exist iff both supports are full
    constructor
    · rintro ⟨f, g, hmax⟩
      obtain ⟨_, -, -, hPfg⟩ := hJ f g hmax
      have hR : ScaledCoupling C ε (FullExp ε f) (FullExp ε g)
          ∈ CompOT.Assignment.couplings a b := hPfg ▸ hP
      have pos := pos_pattern C ε ha hb (fe_nonneg ε f) (fe_nonneg ε g) hR
      exact ⟨fun i => (pos.1 i).1 (fe_pos ε f i), fun j => (pos.2 j).1 (fe_pos ε g j)⟩
    · intro hfs
      have hrep : RepresentsCoupling C ε P (SupportExp a ε f0) (SupportExp b ε g0) :=
        ⟨se_nonneg a ε f0, se_nonneg b ε g0, hPdef⟩
      obtain ⟨-, -, hmaxF, -, -⟩ := hK hfs _ _ hrep
      exact ⟨_, _, hmaxF⟩

end ED71

open ComputationalOTAudit.EntropicDuality in
theorem solution {n m : ℕ}
    (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (CompOT.Assignment.couplings a b).Nonempty ∧
    (PrimalValues C a b ε).Nonempty ∧ BddBelow (PrimalValues C a b ε) ∧
    (FullDualValues C a b ε).Nonempty ∧ BddAbove (FullDualValues C a b ε) ∧
    Nonempty (PositiveSupport a) ∧ Nonempty (PositiveSupport b) ∧
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      CompOT.EntropicLimit.IsEntropicOptimal C a b ε P ∧
      (∀ R, CompOT.EntropicLimit.IsEntropicOptimal C a b ε R → R = P) ∧
      CompOT.EntropicLimit.entObjective C ε P = PrimalValue C a b ε ∧
      PrimalValue C a b ε = sSup (FullDualValues C a b ε) ∧
      (∃ f : PositiveSupport a → ℝ, ∃ g : PositiveSupport b → ℝ,
        IsSupportDualMaximizer C a b ε f g ∧
        SupportDualObjective C a b ε f g = PrimalValue C a b ε) ∧
      (∀ (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ),
        IsSupportDualMaximizer C a b ε f g →
          SupportDualObjective C a b ε f g = PrimalValue C a b ε ∧
          RepresentsCoupling C ε P (SupportExp a ε f) (SupportExp b ε g)) ∧
      (∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
        (∀ i, 0 < u i ↔ 0 < a i) ∧ (∀ j, 0 < v j ↔ 0 < b j) ∧
        IsSupportDualMaximizer C a b ε (SupportLog a ε u) (SupportLog b ε v) ∧
        SupportExp a ε (SupportLog a ε u) = u ∧
        SupportExp b ε (SupportLog b ε v) = v) ∧
      (∀ (u : Fin n → ℝ) (v : Fin m → ℝ), IsFeasibleScaling C a b ε u v →
        ScaledCoupling C ε u v = P ∧
        CompOT.EntropicLimit.IsEntropicOptimal C a b ε (ScaledCoupling C ε u v)) ∧
      ((∃ f : Fin n → ℝ, ∃ g : Fin m → ℝ, IsFullDualMaximizer C a b ε f g) ↔
        FullSupport a ∧ FullSupport b) ∧
      (∀ (f : Fin n → ℝ) (g : Fin m → ℝ), IsFullDualMaximizer C a b ε f g →
        CompOT.EntropicDual.dualObjEnt C a b ε f g = PrimalValue C a b ε ∧
        RepresentsCoupling C ε P (FullExp ε f) (FullExp ε g)) ∧
      (FullSupport a ∧ FullSupport b →
        ∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
          (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
          IsFullDualMaximizer C a b ε (FullLog ε u) (FullLog ε v) ∧
          FullExp ε (FullLog ε u) = u ∧ FullExp ε (FullLog ε v) = v) := by
  exact ED71.main C a b ε hn hm hε ha hb
