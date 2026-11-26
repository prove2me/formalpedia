-- Prove2me | solution 1 for BKAR.ForestIndex.cubeContribution_eq_canonicalGrownForestForSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:17.246969+00:00
-- url     : https://prove2.me/submissions/782e4bf3-412c-4cbe-8a3d-8dced8c4c088

import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_cubeContribution_eq_of_choices


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.ForestIndex
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.ForestIndex
theorem _root_.solution
    (I : ForestIndex V) (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    I.cubeContribution ρ =
      (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ := by
  classical
  unfold cubeContribution
  rw [dif_pos ⟨choices⟩]
  exact
    Forest.canonicalGrownForestForSupport_cubeContribution_eq_of_choices
      (Classical.choice ⟨choices⟩) choices I ρ hρ
end BKAR.ForestIndex
