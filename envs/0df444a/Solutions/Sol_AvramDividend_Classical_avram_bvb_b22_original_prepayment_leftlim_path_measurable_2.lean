-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_b22_original_prepayment_leftlim_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:44:50.619773+00:00
-- url     : https://prove2.me/submissions/3cb311dd-19de-4f58-a40b-e9cc77b0364a

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
  have hJoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD
  have hPair : Measurable (fun t : ℝ≥0 => (t, ω)) :=
    measurable_id.prodMk measurable_const
  simpa only [Function.comp_def] using hJoint.comp hPair
