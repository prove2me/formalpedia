-- Prove2me | solution 1 for FairSelling.minUtil_outcomeOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:51.986983+00:00
-- url     : https://prove2.me/submissions/6bb979ed-319f-4d72-9d48-e0e31c6ebb0d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ) :
    minUtil v (outcomeOf assign m) = minUtilData v assign m := rfl
end FairSelling
