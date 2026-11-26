-- Prove2me | solution 1 for Erdos266.kOf_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:05:14.095801+00:00
-- url     : https://prove2.me/submissions/fd984c18-baec-4ebf-bfaf-8c97ebf35b4e

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_le_kOf_of_cnt_le

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution : Tendsto kOf atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨cnt b, fun a ha => le_kOf_of_cnt_le ha⟩
end Erdos266
