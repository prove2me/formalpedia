-- Prove2me | solution 1 for Erdos1007.nine_edges_card_ge_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:04.355287+00:00
-- url     : https://prove2.me/submissions/05c58855-c018-412a-86e1-8458f3745d4e

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_NineEdges
section
namespace Erdos1007
open SimpleGraph
private lemma edgeFinset_card_le_six_of_card_le_four
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V ≤ 4) : G.edgeFinset.card ≤ 6 := by
  calc
    G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ Nat.choose 4 2 := Nat.choose_le_choose 2 hV
    _ = 6 := by decide
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section
namespace Erdos1007
theorem _root_.solution
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset.card = 9) : 5 ≤ Fintype.card V := by
  by_contra hlt
  have hV : Fintype.card V ≤ 4 := by omega
  have hle : G.edgeFinset.card ≤ 6 := edgeFinset_card_le_six_of_card_le_four hV
  omega
end Erdos1007
