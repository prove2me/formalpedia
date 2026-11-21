-- Prove2me | solution 1 for Cage87.nb_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:26:48.206404+00:00
-- url     : https://prove2.me/submissions/54d01432-80d6-4e24-afa4-889c6a281706

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_wf_ok


set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
variable {v : Nat} (hv : v < 768)
include hv
namespace Cage87
theorem _root_.solution : (nb adj v).length = 8 := by
  have h := wfV_of_wfOk wf_ok v hv
  simp only [wfV, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1
end Cage87
