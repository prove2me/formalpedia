-- Prove2me | solution 1 for Erdos266.tailAnchor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:05:11.32566+00:00
-- url     : https://prove2.me/submissions/66c2d11e-9121-4347-b09e-8be6c30d9f9c

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_bigN_strictMono
public import Theorems.Thm_Erdos266_blockAnchor_nonneg


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {i k : ℕ} (h2i : 2 * i ≤ bigN k) : 0 ≤ tailAnchor i k := by
  refine tsum_nonneg fun l => ?_
  apply blockAnchor_nonneg
  have h1 : bigN k ≤ bigN (k + l) := bigN_strictMono.monotone (by omega)
  have h2 : (2 * i : ℕ) ≤ bigN (k + l) := by omega
  exact_mod_cast h2
end Erdos266
