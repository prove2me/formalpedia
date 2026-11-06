-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:46:27.555055+00:00
-- url     : https://prove2.me/submissions/d2cb76ae-1a63-44e6-add7-23ac98e55a17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A single full-probability event controls all monotone original physical
grids and all nonnegative real cell weights, including those selected after
observing the original Lévy path. No integrability assumption is necessary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u)
        (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i),
        (∑ i : Fin n,
          a i *
            (V (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
             V (riskProcess X x D (u i) ω))) ≤ 0 := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hV : Monotone V :=
    avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
      C hC w V hw_cont hw0 hw_neg hw_smooth hw_grad
      (by intro ht z; simp [V, ht])
      (by intro ht z; simp [V, ht])
  have hR := avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad (0 : ℝ)
  dsimp only at hR ⊢
  filter_upwards [hR] with ω hω
  intro u hu n a ha
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
        ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
        else 0).toReal
  change (∑ i : Fin n,
    a i * (V (riskProcess X x D (u i) ω -
      (R (u (i + 1)) - R (u i))) -
      V (riskProcess X x D (u i) ω))) ≤ 0
  apply Finset.sum_nonpos
  intro i _
  have hRij : R (u i) ≤ R (u (i + 1)) :=
    hω.1 (hu (Nat.le_succ (i : ℕ)))
  have hdec : V (riskProcess X x D (u i) ω -
      (R (u (i + 1)) - R (u i))) ≤
      V (riskProcess X x D (u i) ω) := by
    apply hV
    exact sub_le_self _ (sub_nonneg.mpr hRij)
  exact mul_nonpos_of_nonneg_of_nonpos (ha i) (sub_nonpos.mpr hdec)
