-- Prove2me | solution 1 for FairSelling.cashVal_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:14:48.35199+00:00
-- url     : https://prove2.me/submissions/ecfe094b-9659-49c5-bee2-5083c1eba505

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
theorem _root_.solution (R : Finset G) (w : G → ℝ) (g : G) :
    cashVal R w (some g) = restrictVal R w g := rfl
end FairSelling
