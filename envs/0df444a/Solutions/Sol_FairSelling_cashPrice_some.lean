-- Prove2me | solution 1 for FairSelling.cashPrice_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:06.45999+00:00
-- url     : https://prove2.me/submissions/c192a507-7c69-4dc3-8760-044762308529

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
theorem _root_.solution (R : Finset G) (p : G → ℝ) (c : ℝ) (g : G) :
    cashPrice R p c (some g) = restrictVal R p g := rfl
end FairSelling
