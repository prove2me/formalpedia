-- Prove2me | solution 1 for Erdos266.jOf_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:59:41.284908+00:00
-- url     : https://prove2.me/submissions/f178265c-63c8-4be5-a589-472a57a6b01f

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_kOf_spec
public import Theorems.Thm_Erdos266_cnt_kOf_le

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (n : ℕ) : n - cnt (kOf n) < dOf (kOf n) := by
  have h1 := kOf_spec n
  have h2 := cnt_kOf_le n
  rw [cnt_succ] at h1
  omega
end Erdos266
