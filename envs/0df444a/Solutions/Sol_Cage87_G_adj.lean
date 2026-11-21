-- Prove2me | solution 1 for Cage87.G_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:25:52.419893+00:00
-- url     : https://prove2.me/submissions/ef4ddd09-0285-4b0d-831b-6e4ffb811c9c

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
theorem _root_.solution (u v : Fin 768) : G.Adj u v ↔ v.val ∈ nb adj u.val := Iff.rfl
end Cage87
