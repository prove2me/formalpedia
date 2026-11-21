-- Prove2me | solution 1 for Cage87.nb_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:12.363188+00:00
-- url     : https://prove2.me/submissions/0fc9518d-6e2b-4ef5-9552-86fc678b352f

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_nodup_of_nodupB
public import Theorems.Thm_Cage87_wf_ok


set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
variable {v : Nat} (hv : v < 768)
include hv
namespace Cage87
theorem _root_.solution : (nb adj v).Nodup := by
  have h := wfV_of_wfOk wf_ok v hv
  simp only [wfV, Bool.and_eq_true] at h
  exact nodup_of_nodupB _ h.1.2
end Cage87
