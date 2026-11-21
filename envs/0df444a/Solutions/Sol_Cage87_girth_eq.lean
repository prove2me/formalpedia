-- Prove2me | solution 1 for Cage87.girth_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:28:45.520106+00:00
-- url     : https://prove2.me/submissions/728b131d-cdc2-4c54-9ff3-864e8aeb6c4c

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_seven_le_length
public import Theorems.Thm_Cage87_cycle7_isCycle

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution : G.girth = 7 := by
  have h1 : G.egirth ≤ 7 := cycle7_isCycle.egirth_le_length.trans (by rfl)
  have h2 : 7 ≤ G.egirth := le_egirth.mpr fun a w hw => by exact_mod_cast seven_le_length w hw
  rw [girth, le_antisymm h1 h2]
  rfl
end Cage87
