-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.D_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:56.597827+00:00
-- url     : https://prove2.me/submissions/40fe51b0-8e86-48c9-9b26-5878feb9e4bf

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
theorem _root_.solution (c : ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) : R.D (c • Y) = c • R.D Y := by
  ext i j
  simp only [D, Matrix.of_apply, Matrix.smul_apply]
  rw [← map_smul]; rfl
end CompanionTheory.D.Inhab.HWRep
