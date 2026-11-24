-- Prove2me | solution 1 for FairSelling.cashPrice_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:14:45.259275+00:00
-- url     : https://prove2.me/submissions/457773b7-425f-4465-b722-364d1811fdae

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
theorem _root_.solution (R : Finset G) (p : G → ℝ) (c : ℝ) :
    cashPrice R p c none = c := rfl
end FairSelling
