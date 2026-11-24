-- Prove2me | solution 1 for FairSelling.sum_price_le_vbarSum
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:18:35.965811+00:00
-- url     : https://prove2.me/submissions/8e3624f7-bccd-49c8-92ae-c1491fc0ba89

import Mathlib
import Definitions.Def_RequestProject_Selling
open FairSelling
variable {G : Type*}


theorem solution (w p : G → ℝ) (Y : Finset G) :
    ∑ g ∈ Y, p g ≤ vbarSum w p Y := by
  exact Finset.sum_le_sum fun g _ => le_max_left _ _
