-- Prove2me | solution 1 for FairSelling.four_thr_le_vbarSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:49.279316+00:00
-- url     : https://prove2.me/submissions/38019fa0-2c81-41b8-a5c8-7346b558f6bc

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_three_MMS_le_vbarSum_univ


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    4 * ((3 / 4 : ℝ) * MMS 3 w p) ≤ vbarSum w p Finset.univ := by
  have := three_MMS_le_vbarSum_univ w p hw hp
  linarith
end FairSelling
