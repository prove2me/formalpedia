-- Prove2me | solution 1 for FairSelling.util_swapOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:07.127415+00:00
-- url     : https://prove2.me/submissions/90e2479e-7593-4d39-9fec-e8821cdbe3ba

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w : G → ℝ) (o : Outcome G 2) (j : Fin 2) :
    util w (swapOutcome o) j = util w o (Equiv.swap 0 1 j) := rfl
end FairSelling
