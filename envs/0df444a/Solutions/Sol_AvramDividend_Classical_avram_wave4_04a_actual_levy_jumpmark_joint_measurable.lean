-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:57:06.085334+00:00
-- url     : https://prove2.me/submissions/28ecfe1f-96d8-47b6-a1f9-7390fc04998d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_prejump_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω =>
      X.X z.1 z.2 - Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) := by
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation X.X
      (fun t => (X.adapted t).mono (𝓕.le t) le_rfl) X.rightCont
  exact hX.sub (avram_wave4_04a_actual_levy_prejump_joint_measurable X)
