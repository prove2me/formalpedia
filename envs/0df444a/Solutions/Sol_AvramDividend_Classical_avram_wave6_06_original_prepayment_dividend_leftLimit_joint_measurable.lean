-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:18:31.299209+00:00
-- url     : https://prove2.me/submissions/2ab2cda6-e565-446a-8736-4fe99f134b7a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_has_leftLimits
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Actual original D+ has a jointly measurable prepayment left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => rightLimit D s z.2) z.1) := by
  have hJoint : Measurable
      (fun z : ℝ≥0 × Ω => rightLimit D z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation
      (fun t ω => rightLimit D t ω)
      (fun t => dividendStrategy_rightLimit_measurable D hD t)
      (fun ω t => dividendStrategy_rightLimit_rightContinuous D hD ω t)
  have hZero : Measurable (fun ω : Ω =>
      Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (0 : ℝ≥0)) := by
    have heq : (fun ω : Ω =>
        Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (0 : ℝ≥0)) =
        (fun ω : Ω => rightLimit D 0 ω) := by
      funext ω
      exact leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from isBot_bot)
    rw [heq]
    exact dividendStrategy_rightLimit_measurable D hD 0
  exact avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
    (fun t ω => rightLimit D t ω) hJoint hZero
    (fun ω t ht => dividendStrategy_rightLimit_has_leftLimits D hD ω t ht)
