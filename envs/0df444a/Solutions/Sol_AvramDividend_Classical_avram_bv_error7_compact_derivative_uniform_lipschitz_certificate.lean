-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_compact_derivative_uniform_lipschitz_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:45:14.132346+00:00
-- url     : https://prove2.me/submissions/efe93848-0545-4568-92de-775d694bde19

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_continuous_deriv_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A compact interval of differentiability with continuous derivative
has one common Lipschitz constant and derivative bound. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hDiff : ∀ y ∈ Set.Icc a b, DifferentiableAt ℝ w y)
    (hDerCont : ContinuousOn (deriv w) (Set.Icc a b)) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
        |w z - w y| ≤ L * |z - y|) ∧
      (∀ y ∈ Set.Icc a b, |deriv w y| ≤ L) := by
  obtain ⟨L, hL, hDeriv⟩ :=
    avram_bv_error7_compact_continuous_deriv_uniform_bound
      w a b hDerCont
  refine ⟨L, hL, ?_, hDeriv⟩
  intro y hy z hz
  have hNormDeriv : ∀ t ∈ Set.Icc a b, ‖deriv w t‖ ≤ L := by
    intro t ht
    simpa only [Real.norm_eq_abs] using hDeriv t ht
  have h :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hDiff hNormDeriv (convex_Icc a b) hy hz
  simpa only [Real.norm_eq_abs] using h
