-- Prove2me | solution 1 for Cage87.cycle7_isCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:27.742191+00:00
-- url     : https://prove2.me/submissions/8f1e1ac1-ef49-45fa-bcb2-8eca047a13a3

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution : cycle7.IsCycle := by
  rw [cycle7, Walk.cons_isCycle_iff, Walk.isPath_def]
  constructor
  · decide +kernel
  · decide +kernel
end Cage87
