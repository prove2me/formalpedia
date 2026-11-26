-- Prove2me | solution 1 for Continuous.borel_borel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:46.391746+00:00
-- url     : https://prove2.me/submissions/0202bf43-fb1c-445c-8732-237aeea90247

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace Continuous
theorem _root_.solution
    {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    @Measurable X Y (borel X) (borel Y) f := by
  intro s hs
  induction hs with
  | basic s hs => exact MeasurableSpace.measurableSet_generateFrom (hf.isOpen_preimage _ hs)
  | empty => exact @MeasurableSet.empty X (borel X)
  | compl _ _ ih => exact ih.compl
  | iUnion _ _ ih => rw [Set.preimage_iUnion]; exact .iUnion ih
end Continuous
