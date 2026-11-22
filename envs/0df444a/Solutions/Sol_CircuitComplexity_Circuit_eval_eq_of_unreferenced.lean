-- Prove2me | solution 1 for CircuitComplexity.Circuit.eval_eq_of_unreferenced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:29.595215+00:00
-- url     : https://prove2.me/submissions/6d84f939-1335-42bb-a929-af37fe5c8ad3

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_eq_of_unreferenced
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno_gates : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (hno_outputs : ∀ j : Fin M, ∀ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val ≠ i.val)
    (x : BitString N) :
    c.eval x = c.eval (Function.update x i b) := by
  funext j; simp only [eval, Gate.eval]
  congr 1; funext k; congr 1
  exact wireValue_eq_of_unreferenced c i b hno_gates x _ (hno_outputs j k)
end CircuitComplexity.Circuit
