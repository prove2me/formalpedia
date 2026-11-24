-- Prove2me | solution 2 for FairSelling.sum_price_le_vbarSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:45.917847+00:00
-- url     : https://prove2.me/submissions/9f790b7d-dbaa-4313-bb29-f2337adb9d46

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (Y : Finset G) :
    ∑ g ∈ Y, p g ≤ vbarSum w p Y :=
  Finset.sum_le_sum (fun _ _ => le_max_left _ _)
end FairSelling
