-- Prove2me | solution 1 for FD1D.refreshedLaw_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:44:45.728821+00:00
-- url     : https://prove2.me/submissions/cc4db222-cbcb-4b05-ae03-b3dff59f050d

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_assignmentState_perm
import Theorems.Thm_FD1D_refreshedLaw_lawInvariant_of_compatible

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution {L m : ℕ}
    (leafPerm : Equiv.Perm (DyadicNode L)) :
    FiniteKernel.LawInvariant (refreshedLaw L m)
      (inventoryStatePerm leafPerm) :=
  refreshedLaw_lawInvariant_of_compatible leafPerm
    (inventoryStatePerm leafPerm) (assignmentState_perm leafPerm)
end FD1D
