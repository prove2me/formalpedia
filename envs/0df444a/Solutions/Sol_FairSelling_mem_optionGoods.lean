-- Prove2me | solution 1 for FairSelling.mem_optionGoods
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:07.13377+00:00
-- url     : https://prove2.me/submissions/ed95c4c1-b3ec-4824-91bd-c513f6a9e125

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution {s : Finset (Option G)} {g : G} :
    g ∈ optionGoods s ↔ some g ∈ s := by
  unfold optionGoods;
  grind +qlia
end FairSelling
