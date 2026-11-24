-- Prove2me | solution 1 for FairSelling.cashVal_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:14:23.760232+00:00
-- url     : https://prove2.me/submissions/4bbc1e0d-26ea-4ad0-b639-08eac770b5b6

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (R : Finset G) (w : G → ℝ) : cashVal R w none = 0 := rfl
end FairSelling
