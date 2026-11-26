-- Prove2me | solution 1 for Erdos266.tSeq_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:36:17.753926+00:00
-- url     : https://prove2.me/submissions/a41f6a71-c2f5-4879-8a86-94af0dfcce18

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
public import Theorems.Thm_Erdos266_tSeq_not_mem_picks
public import Theorems.Thm_Erdos266_mem_picks

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution : Function.Injective tSeq := by
  intro a b hab
  by_contra hne
  wlog h : a < b generalizing a b
  · exact this hab.symm (Ne.symm hne) ((Ne.lt_or_gt hne).resolve_left h)
  exact tSeq_not_mem_picks b (mem_picks.mpr ⟨a, h, hab⟩)
end Erdos266
