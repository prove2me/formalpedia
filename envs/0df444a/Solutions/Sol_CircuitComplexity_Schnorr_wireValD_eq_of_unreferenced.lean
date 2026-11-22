-- Prove2me | solution 1 for CircuitComplexity.Schnorr.wireValD_eq_of_unreferenced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:07.371332+00:00
-- url     : https://prove2.me/submissions/6b29d677-09e6-47a0-813d-b5c048778b2a

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution
    {N s : Nat} (d : CircDesc N s) (a : Fin N) (b : Bool)
    (hno : ∀ g : Fin s, (d g).2.1.1.val ≠ a.val ∧ (d g).2.1.2.val ≠ a.val)
    (x : BitString N) (w : Fin (N + s)) (hw : w.val ≠ a.val) :
    wireValD d x w = wireValD d (Function.update x a b) w := by
  by_cases hw_lt : w.val < N
  · -- Primary input
    conv_lhs => rw [wireValD]
    conv_rhs => rw [wireValD]
    simp only [hw_lt, dite_true]
    exact (Function.update_of_ne (show (⟨w.val, hw_lt⟩ : Fin N) ≠ a from
      fun h => hw (congrArg Fin.val h)) b x).symm
  · -- Gate wire
    have hi : w.val - N < s := by omega
    obtain ⟨hw1, hw2⟩ := hno ⟨w.val - N, hi⟩
    have hrec1 : ∀ (h : (d ⟨w.val - N, hi⟩).2.1.1.val < w.val),
        wireValD d x ⟨(d ⟨w.val - N, hi⟩).2.1.1.val, by omega⟩ =
        wireValD d (Function.update x a b) ⟨(d ⟨w.val - N, hi⟩).2.1.1.val, by omega⟩ :=
      fun _ => solution d a b hno x _ hw1
    have hrec2 : ∀ (h : (d ⟨w.val - N, hi⟩).2.1.2.val < w.val),
        wireValD d x ⟨(d ⟨w.val - N, hi⟩).2.1.2.val, by omega⟩ =
        wireValD d (Function.update x a b) ⟨(d ⟨w.val - N, hi⟩).2.1.2.val, by omega⟩ :=
      fun _ => solution d a b hno x _ hw2
    conv_lhs => rw [wireValD]
    conv_rhs => rw [wireValD]
    simp only [hw_lt, dite_false]
    simp_all
termination_by w.val
end CircuitComplexity.Schnorr
