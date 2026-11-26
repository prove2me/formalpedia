-- Prove2me | solution 1 for Erdos266.m_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:34.754039+00:00
-- url     : https://prove2.me/submissions/ce714489-e3ef-4d7f-8f79-28f7eaa26dc2

module
public import Definitions.Def_Erdos266_Enumeration
public import Definitions.Def_Erdos266_Defs
public import Theorems.Thm_Erdos266_tSeq_injective


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (i j : ℕ) : m i j ≠ 0 := by
  refine inv_ne_zero (prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr ?_)
  exact fun h => (mem_erase.mp hk).1 (tSeq_injective h)
end Erdos266
