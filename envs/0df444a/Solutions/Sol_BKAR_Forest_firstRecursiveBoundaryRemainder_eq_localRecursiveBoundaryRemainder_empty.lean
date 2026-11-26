-- Prove2me | solution 1 for BKAR.Forest.firstRecursiveBoundaryRemainder_eq_localRecursiveBoundaryRemainder_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:23.341797+00:00
-- url     : https://prove2.me/submissions/c8714c94-3c87-4ee7-983f-5660c7c10476

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    firstRecursiveBoundaryRemainder choices ρ =
      localRecursiveBoundaryRemainder choices (Forest.empty V) [] [] 1 ρ :=
  rfl
end BKAR.Forest
