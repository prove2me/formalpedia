-- Prove2me | solution 1 for Erdos1007.nine_edges_minDegree_three_card_le_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:05.525967+00:00
-- url     : https://prove2.me/submissions/745493b0-2dbd-4e61-a108-d952998f2a71

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
private lemma sum_degrees_eq_eighteen
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) : ∑ v, G.degree v = 18 := by
  rw [G.sum_degrees_eq_twice_card_edges, hE]
private lemma three_mul_card_le_sum_degrees
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v) : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
  calc
    3 * Fintype.card V = ∑ _v : V, 3 := by
      rw [Nat.mul_comm, ← Finset.card_univ, ← Finset.sum_const_nat fun _ _ => rfl]
    _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
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
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Fintype.card V ≤ 6 := by
  have hsum : ∑ v, G.degree v = 18 := sum_degrees_eq_eighteen hE
  have hlow : 3 * Fintype.card V ≤ ∑ v, G.degree v := three_mul_card_le_sum_degrees hdeg
  omega
end Erdos1007
