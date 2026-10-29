-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_origin_dyadic_cauchy_ae_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:16:33.613057+00:00
-- url     : https://prove2.me/submissions/d651044c-ae20-4d76-8c74-702429992adf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_positive_interval_restricted_volume_ne_zero_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_positive_time_restrict_support_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_joint_real_cauchy_event_meas_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_equal_event_measure_ae_equiv_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_supported_stationary_fubini_ws01c

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      CauchySeq (fun n : ℕ =>
        X.drift -
          (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) /
            (((1 : ℝ≥0) / 2) ^ n : ℝ)) := by
  have hP := X.isProbability
  have hne : NeZero (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨bv_positive_interval_restricted_volume_ne_zero_ws01c⟩
  have hJ := bv_actual_joint_real_cauchy_event_meas_ws01c X
  have hsec : ∀ t : ℝ, MeasurableSet {ω | CauchySeq (fun n : ℕ =>
      X.drift - (X.X (Real.toNNReal t + ((1 : ℝ≥0) / 2) ^ n) ω - X.X (Real.toNNReal t) ω) /
        (((1 : ℝ≥0) / 2) ^ n : ℝ))} := fun t => measurable_prodMk_left hJ
  have key := bv_supported_stationary_fubini_ws01c (volume.restrict (Ioc (0 : ℝ) 1)) P
    (Ioc (0 : ℝ) 1) bv_positive_time_restrict_support_ws01c 0
    (fun t ω => CauchySeq (fun n : ℕ =>
      X.drift - (X.X (Real.toNNReal t + ((1 : ℝ≥0) / 2) ^ n) ω - X.X (Real.toNNReal t) ω) /
        (((1 : ℝ≥0) / 2) ^ n : ℝ))) hJ
    (bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c X hBV) ?_
  · simpa using key
  · intro t _
    apply bv_equal_event_measure_ae_equiv_ws01c P _ _ (hsec t) (hsec 0)
    rw [bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c X (Real.toNNReal t)]
    simp
