-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB316_original_postpayment_reserve_physical_time_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:08:29.591499+00:00
-- url     : https://prove2.me/submissions/40287d18-bb67-47bd-b874-271cc0671458

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original postpayment reserve has measurable physical-time sections. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    Measurable (fun t : ℝ =>
      x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω) := by
  exact (avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
    X x D hD).comp (measurable_real_toNNReal.prodMk measurable_const)
