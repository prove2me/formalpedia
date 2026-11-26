-- Prove2me | solution 1 for FD1D.refreshedLaw_lawInvariant_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:17.168802+00:00
-- url     : https://prove2.me/submissions/bc6b0741-f351-4d58-a856-4e9dcfe0fca0

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_uniform_map_lawInvariant

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L m : ℕ} (leafPerm : Equiv.Perm (DyadicNode L))
    (statePerm : Equiv.Perm (InventoryState (DyadicNode L) m))
    (hcompat : ∀ ω : DyadicAssignment L m,
      assignmentState (assignmentPerm leafPerm ω) =
        statePerm (assignmentState ω)) :
    FiniteKernel.LawInvariant (refreshedLaw L m) statePerm :=
  uniform_map_lawInvariant assignmentState (assignmentPerm leafPerm)
    statePerm hcompat
end FD1D
