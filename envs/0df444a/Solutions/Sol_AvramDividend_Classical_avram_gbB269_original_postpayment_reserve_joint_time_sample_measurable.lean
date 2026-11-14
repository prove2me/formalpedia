-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:42:51.854679+00:00
-- url     : https://prove2.me/submissions/22897061-0d13-4433-9e6d-bc5e0990cbf1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section

/-- Exact original postpayment reserve is jointly Borel measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hSection : ∀ t : ℝ≥0, Measurable
      (fun ω : Ω => x + X.X t ω - rightLimit D t ω) := by
    intro t
    have hXt : Measurable (fun ω : Ω => X.X t ω) :=
      hXJoint.comp (measurable_const.prodMk measurable_id)
    exact (measurable_const.add hXt).sub
      (dividendStrategy_rightLimit_measurable D hD t)
  have hRight := (postPaymentReserve_cadlag_adapted X x D hD).1
  exact rightContinuous_measurable_sections_joint_evaluation
    (fun t ω => x + X.X t ω - rightLimit D t ω) hSection hRight
