-- Prove2me | solution 1 for Erdos266.tailAnchor_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:51:03.184823+00:00
-- url     : https://prove2.me/submissions/f8029d3b-bd6d-4e0f-8cf1-7e02194c74e2

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (i : ℕ) :
    Filter.Tendsto (fun k => tailAnchor i k) Filter.atTop (nhds 0) := by
  have h := tendsto_sum_nat_add (f := fun l => blockAnchor i l)
  refine h.congr fun k => ?_
  rw [tailAnchor]
  exact tsum_congr fun l => by rw [Nat.add_comm]
end Erdos266
