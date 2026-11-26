-- Prove2me | solution 1 for Erdos266.tailAnchor_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:52:19.323905+00:00
-- url     : https://prove2.me/submissions/590cf1be-b94a-4f6c-9544-78b6fe8a0462

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_summable_blockAnchor

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i : ℕ} (hi : 1 ≤ i) (k : ℕ) :
    tailAnchor i k = blockAnchor i k + tailAnchor i (k + 1) := by
  have hsum : Summable (fun l => blockAnchor i (k + l)) := by
    have h := summable_blockAnchor hi (i := i)
    exact ((summable_nat_add_iff k).mpr h).congr fun l => by rw [Nat.add_comm l k]
  have h2 : ∑' (b : ℕ), blockAnchor i (k + (b + 1)) = tailAnchor i (k + 1) := by
    rw [tailAnchor]
    exact tsum_congr fun b => by congr 1; omega
  rw [tailAnchor, hsum.tsum_eq_zero_add, Nat.add_zero, h2]
end Erdos266
