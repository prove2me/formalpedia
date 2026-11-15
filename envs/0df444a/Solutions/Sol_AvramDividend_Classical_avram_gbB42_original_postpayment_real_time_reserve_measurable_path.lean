-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB42_original_postpayment_real_time_reserve_measurable_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:52:44.40495+00:00
-- url     : https://prove2.me/submissions/0edde682-fd1d-49c5-a9d9-5e97dd6a9cae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ ω : Ω, Measurable (fun t : ℝ =>
      x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω) := by
  intro ω
  have hm : Measurable (fun t : ℝ => ((Real.toNNReal t), ω)) := by
    measurability
  exact
    (avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
      X x D hD).comp hm
