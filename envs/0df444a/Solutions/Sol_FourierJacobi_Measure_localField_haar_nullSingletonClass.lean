-- Prove2me | solution 1 for FourierJacobi.Measure.localField_haar_nullSingletonClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:42.616803+00:00
-- url     : https://prove2.me/submissions/648660e0-5f51-4653-a522-0214d4c8dbc0

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_localField_punctured_nhds

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
namespace FourierJacobi.Measure
theorem _root_.solution : NullSingletonClass μ := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let : (𝓝[≠] (0 : K)).NeBot := localField_punctured_nhds K
  infer_instance
end FourierJacobi.Measure
