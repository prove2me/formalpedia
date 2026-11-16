-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:56:23.796098+00:00
-- url     : https://prove2.me/submissions/b1123126-6d01-4950-a3e7-194b053fd5c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
import Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_negative_kernel_uniform_domination_data
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    Tendsto
      (fun n : ℕ =>
        ∫ z in Iio (0 : ℝ),
          w (C.toReal / ((n : ℝ) + 2) + z) -
            w (C.toReal / ((n : ℝ) + 2)) ∂X.ν)
      atTop
      (𝓝 (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)) := by
  let y : ℕ → ℝ := fun n => C.toReal / ((n : ℝ) + 2)
  have hy : Tendsto y atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (tendsto_const_div_atTop_nhds_zero_nat C.toReal).comp
        (Filter.tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def, y, Nat.cast_add, Nat.cast_ofNat] using hShift
  have hyPos : ∀ n, 0 ≤ y n := by
    intro n
    dsimp [y]
    exact div_nonneg ENNReal.toReal_nonneg (by positivity)
  have hPoint : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      Tendsto (fun n => w (y n + z) - w (y n))
        atTop (𝓝 (w ((0 : ℝ) + z) - w 0)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Iio)] with z hz
    simpa only [zero_add] using
      (avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
        w y hy hyPos hwCont hwNeg z hz)
  obtain ⟨g, hg, hMeas, hDom⟩ :=
    avram_bvb46_original_negative_kernel_uniform_domination_data
      X hActivity w C hC hFinite hwCont hwNeg
  have hDCT :=
    tendsto_integral_of_dominated_convergence g
      hMeas hg hDom hPoint
  simpa only [y, zero_add] using hDCT
