-- Prove2me | solution 1 for FD1D.iterate_refreshedLaw_lawInvariant_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:35.862166+00:00
-- url     : https://prove2.me/submissions/dacd01c2-4a8a-47a4-b36c-3d13e4281296

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_refreshedLaw_lawInvariant_of_compatible
import Theorems.Thm_FD1D_FiniteKernel_iterate_lawInvariant


set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L m : ℕ} (K : FiniteKernel (InventoryState (DyadicNode L) m))
    (leafPerm : Equiv.Perm (DyadicNode L))
    (statePerm : Equiv.Perm (InventoryState (DyadicNode L) m))
    (hcompat : ∀ ω : DyadicAssignment L m,
      assignmentState (assignmentPerm leafPerm ω) =
        statePerm (assignmentState ω))
    (hK : K.Equivariant statePerm) (n : ℕ) :
    FiniteKernel.LawInvariant (K.iterate n (refreshedLaw L m)) statePerm :=
  FiniteKernel.iterate_lawInvariant hK
    (refreshedLaw_lawInvariant_of_compatible leafPerm statePerm hcompat) n
end FD1D
