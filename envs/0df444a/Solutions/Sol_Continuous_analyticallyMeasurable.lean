-- Prove2me | solution 1 for Continuous.analyticallyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:45.051346+00:00
-- url     : https://prove2.me/submissions/29886d21-30ef-46b8-af3e-ecf09825f7f3

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Theorems.Thm_MeasureTheory_AnalyticSet_mem_analyticMeasurableSpace
import Theorems.Thm_IsOpen_analyticSet

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace Continuous
theorem _root_.solution
    [PolishSpace X]
    {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : AnalyticallyMeasurable f := by
  intro s hs
  induction hs with
  | basic s hs => exact (hf.isOpen_preimage _ hs).analyticSet.mem_analyticMeasurableSpace
  | empty => exact @MeasurableSet.empty X (analyticMeasurableSpace X)
  | compl _ _ ih => exact ih.compl
  | iUnion _ _ ih => rw [Set.preimage_iUnion]; exact .iUnion ih
end Continuous
