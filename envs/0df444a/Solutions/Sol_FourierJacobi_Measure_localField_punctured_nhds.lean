-- Prove2me | solution 1 for FourierJacobi.Measure.localField_punctured_nhds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:55.120944+00:00
-- url     : https://prove2.me/submissions/81a19a05-1190-4455-b204-2f7fe10b7d54

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Measure
theorem _root_.solution : (𝓝[≠] (0 : K)).NeBot := by
  rw [nhdsWithin_neBot]
  intro s hs
  obtain ⟨γ, hγ, hγs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
  obtain ⟨b, hb⟩ := ValuativeRel.valuation_surjective γ
  have hb0 : b ≠ 0 := by
    intro h
    apply hγ
    rw [← hb, h, map_zero]
  obtain ⟨a, ha0, ha⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
  refine ⟨b * a, hγs ?_, by simpa using mul_ne_zero hb0 ha0⟩
  change ValuativeRel.valuation K (b * a) < γ
  rw [map_mul, hb]
  simpa using mul_lt_mul_of_pos_left ha (pos_iff_ne_zero.mpr hγ)
end FourierJacobi.Measure
