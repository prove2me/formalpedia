-- Prove2me | solution 1 for BKAR.Forest.pairwise_aedisjoint_orderedCubeSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:05.383623+00:00
-- url     : https://prove2.me/submissions/dcc03d81-8f0d-4efc-9bb0-c30865269c56

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_aedisjoint_orderedCubeSimplex_of_ne
import Theorems.Thm_BKAR_ForestIndex_ext


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    Pairwise
      (fun order₁ order₂ : {order : List (Edge V) // order ∈ F.edgeOrders} =>
        AEDisjoint (volume : Measure (F.EdgeParam → ℝ))
          (F.orderedCubeSimplex order₁.val)
          (F.orderedCubeSimplex order₂.val)) := by
  intro order₁ order₂ hne
  exact F.aedisjoint_orderedCubeSimplex_of_ne
    order₁.property order₂.property
    (fun hval => hne (Subtype.ext hval))
end BKAR.Forest
