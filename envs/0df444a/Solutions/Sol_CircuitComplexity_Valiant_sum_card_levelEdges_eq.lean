-- Prove2me | solution 1 for CircuitComplexity.Valiant.sum_card_levelEdges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:04.907837+00:00
-- url     : https://prove2.me/submissions/fb7503b4-de81-46fc-97bf-4e542206223e

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
public import Theorems.Thm_CircuitComplexity_Valiant_one_le_canonicalLabel
public import Theorems.Thm_CircuitComplexity_Valiant_canonicalLabel_le_depth
public import Theorems.Thm_CircuitComplexity_Valiant_canonicalLabel_isLegal
public import Theorems.Thm_Digraph_mem_edgeFinset

section
@[expose] public section
namespace Digraph
end Digraph
namespace CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
private lemma canonicalLabel_sub_one_lt_two_pow
    (G : Digraph V) (hac : IsAcyclic G) {k : ℕ} (hd : G.depth ≤ 2 ^ k)
    (v : V) : G.canonicalLabel v - 1 < 2 ^ k := by
  have h1 := (canonicalLabel_le_depth G hac v).trans hd
  have h2 := one_le_canonicalLabel G v
  omega
section LegalLabelHelpers
variable {V : Type*}
end LegalLabelHelpers
omit [Fintype V] in
/-- For `x ≠ y` both below `2 ^ k`, `firstDifferBit k x y` lies in
`{1,...,k}` and `k - firstDifferBit k x y = Nat.log2 (x ^^^ y)`. -/
private lemma firstDifferBit_of_ne
    {k x y : ℕ} (hxne : x ≠ y) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    1 ≤ firstDifferBit k x y ∧
    firstDifferBit k x y ≤ k ∧
    k - firstDifferBit k x y = Nat.log2 (x ^^^ y) := by
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  have hxor_lt : x ^^^ y < 2 ^ k := Nat.xor_lt_two_pow hx hy
  have hlog_lt : Nat.log2 (x ^^^ y) < k := (Nat.log2_lt hxor_ne).mpr hxor_lt
  simp only [firstDifferBit, if_neg hxne]
  omega
variable [DecidableEq V]
private lemma firstDifferBit_mem_Ioc
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k)
    {e : V × V} (he : e ∈ G.edgeFinset) :
    firstDifferBit k (G.canonicalLabel e.1 - 1) (G.canonicalLabel e.2 - 1) ∈
      Finset.Ioc 0 k := by
  have huv : G.Adj e.1 e.2 := Digraph.mem_edgeFinset.mp he
  have h12 : G.canonicalLabel e.1 < G.canonicalLabel e.2 :=
    canonicalLabel_isLegal G hac _ _ huv
  have h1' : 1 ≤ G.canonicalLabel e.1 := one_le_canonicalLabel G _
  have hab : G.canonicalLabel e.1 - 1 ≠ G.canonicalLabel e.2 - 1 := by omega
  obtain ⟨hpos, hle, _⟩ := firstDifferBit_of_ne hab
    (canonicalLabel_sub_one_lt_two_pow G hac hd _)
    (canonicalLabel_sub_one_lt_two_pow G hac hd _)
  exact Finset.mem_Ioc.mpr ⟨hpos, hle⟩
end CircuitComplexity.Valiant
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace CircuitComplexity.Valiant
theorem _root_.solution
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k) :
    ∑ i ∈ Finset.Ioc 0 k, (levelEdges G k i).card = G.edgeFinset.card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun e he => firstDifferBit_mem_Ioc G hac hd he)
end CircuitComplexity.Valiant
