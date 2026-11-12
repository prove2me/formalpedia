-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b22_original_prepayment_leftlim_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:44:22.679447+00:00
-- url     : https://prove2.me/submissions/a7b7faef-2b58-43f2-b7a4-4fde895da38d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original prepayment reserve left limit is Borel measurable on each physical path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
  have htime : Measurable (fun t : ℝ≥0 => (t, ω)) :=
    measurable_id.prodMk measurable_const
  exact (avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
    X x D hD).comp htime
