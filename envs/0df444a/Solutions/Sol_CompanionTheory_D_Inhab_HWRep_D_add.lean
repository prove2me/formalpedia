-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.D_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:55.912784+00:00
-- url     : https://prove2.me/submissions/ef04f7a9-e973-46e4-83ee-81cd736f5ef4

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)
namespace CompanionTheory.D.Inhab.HWRep
theorem _root_.solution (Y Z : Matrix (Fin k) (Fin k) ℂ) : R.D (Y + Z) = R.D Y + R.D Z := by
  ext i j
  simp only [D, Matrix.of_apply, Matrix.add_apply]
  rw [← map_add]; rfl
end CompanionTheory.D.Inhab.HWRep
