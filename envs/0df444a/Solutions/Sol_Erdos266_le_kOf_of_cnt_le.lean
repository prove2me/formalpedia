-- Prove2me | solution 1 for Erdos266.le_kOf_of_cnt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:01:14.184861+00:00
-- url     : https://prove2.me/submissions/244721a3-a06b-4571-befc-d8a5dc1b6f1b

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_cnt_mono
public import Theorems.Thm_Erdos266_kOf_spec

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {n k : ℕ} (h : cnt k ≤ n) : k ≤ kOf n := by
  by_contra hc
  push Not at hc
  have h1 : kOf n + 1 ≤ k := by omega
  have h2 : cnt (kOf n + 1) ≤ cnt k := cnt_mono h1
  have h3 := kOf_spec n
  omega
end Erdos266
