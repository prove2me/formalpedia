-- Prove2me | solution 1 for BKAR.Forest.pairCoordOfOrder_pairMeasurableEquivOfPair_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:14.172804+00:00
-- url     : https://prove2.me/submissions/bb92936f-82a2-4ea6-8b49-432e4446ab8f

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_pairMeasurableEquivOfPair_apply

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (z : ℝ × ℝ) :
    F.pairCoordOfOrder e₁ e₂
        ((F.pairMeasurableEquivOfPair hedges hne).symm z) = z := by
  rw [← F.pairMeasurableEquivOfPair_apply hedges hne
    ((F.pairMeasurableEquivOfPair hedges hne).symm z)]
  exact (F.pairMeasurableEquivOfPair hedges hne).apply_symm_apply z
end BKAR.Forest
