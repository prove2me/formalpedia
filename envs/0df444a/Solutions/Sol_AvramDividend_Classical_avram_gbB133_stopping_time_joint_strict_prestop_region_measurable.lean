-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB133_stopping_time_joint_strict_prestop_region_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:22:14.379681+00:00
-- url     : https://prove2.me/submissions/678f576a-ccb1-46f8-80a8-dee10dc4e82b

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    MeasurableSet {z : ℝ≥0 × Ω | z.1 < ρ z.2} := by
  have hm : Measurable (fun ω : Ω => (ρ ω : WithTop ℝ≥0)) :=
    hρstop.measurable'
  have hleft : Measurable (fun z : ℝ≥0 × Ω => (z.1 : WithTop ℝ≥0)) :=
    WithTop.measurable_coe.comp measurable_fst
  have hright : Measurable (fun z : ℝ≥0 × Ω => (ρ z.2 : WithTop ℝ≥0)) :=
    hm.comp measurable_snd
  simpa only [WithTop.coe_lt_coe] using (measurableSet_lt hleft hright)
