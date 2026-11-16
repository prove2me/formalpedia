-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:44:57.737201+00:00
-- url     : https://prove2.me/submissions/4e25e55d-bb62-4c96-b126-671451037649

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_negative_kernel_uniform_domination_data
import Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_negative_kernel_zero_reserve_pointwise_ae_tendsto
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
      (𝓝 (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν))  := by
  obtain ⟨g, hg, hMeas, hDom⟩ :=
    avram_bvb46_original_negative_kernel_uniform_domination_data
      X hActivity w C hC hFinite hwCont hwNeg
  have hLim :=
    avram_bvb47_original_negative_kernel_zero_reserve_pointwise_ae_tendsto
      X hActivity w C hC hFinite hwCont hwNeg
  exact tendsto_integral_of_dominated_convergence g hMeas hg hDom hLim
