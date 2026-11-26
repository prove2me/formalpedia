-- Prove2me | solution 1 for C6BipartiteDomination.neighborsIn_self_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:15.524802+00:00
-- url     : https://prove2.me/submissions/46ab89ff-5e2b-4685-a724-098237a71f77

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (S T : Finset V) :
    neighborsIn G S T ⊆ T := by
  classical
  intro w hw
  exact (mem_neighborsIn G S T w).mp hw |>.1
end C6BipartiteDomination
