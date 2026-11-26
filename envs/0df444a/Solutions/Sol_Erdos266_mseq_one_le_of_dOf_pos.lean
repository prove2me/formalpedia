-- Prove2me | solution 1 for Erdos266.mseq_one_le_of_dOf_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:58.63131+00:00
-- url     : https://prove2.me/submissions/251d65b3-f385-4239-acb6-5385856057b7

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_dOf_lt_iff
public import Theorems.Thm_Erdos266_dOf_lt_two


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {l : ℕ} (h : 0 < dOf l) : mseq 1 ≤ l := by
  by_contra hc
  push Not at hc
  rcases Nat.lt_or_ge l 2 with h2 | h2
  · rw [dOf_lt_two h2] at h
    omega
  · have := (dOf_lt_iff h2).mpr hc
    omega
end Erdos266
