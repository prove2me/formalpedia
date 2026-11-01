-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_prepayment_controlled_source_leftjump_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:51:03.256212+00:00
-- url     : https://prove2.me/submissions/c30c5a17-d066-4096-9792-64bf8bd42449

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        riskProcess X x D z.1 z.2 -
          Function.leftLim
            (fun s : ℝ≥0 => riskProcess X x D s z.2) z.1
      else (0 : ℝ)) := by
  have hpos : MeasurableSet {z : ℝ≥0 × Ω | (0 : ℝ≥0) < z.1} := by
    have hIoi : MeasurableSet (Ioi (0 : ℝ≥0)) := measurableSet_Ioi
    exact hIoi.preimage measurable_fst
  have hsource : Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        X.X z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1
      else (0 : ℝ)) :=
    (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).ite
      hpos measurable_const
  have hpoint : (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        riskProcess X x D z.1 z.2 -
          Function.leftLim
            (fun s : ℝ≥0 => riskProcess X x D s z.2) z.1
      else (0 : ℝ)) =
      (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        X.X z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1
      else (0 : ℝ)) := by
    funext z
    split_ifs with ht
    · exact avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
        X x D hD z.2 z.1 ht
    · rfl
  rw [hpoint]
  exact hsource