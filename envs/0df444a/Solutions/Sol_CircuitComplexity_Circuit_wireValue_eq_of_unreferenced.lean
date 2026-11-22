-- Prove2me | solution 1 for CircuitComplexity.Circuit.wireValue_eq_of_unreferenced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:48.281069+00:00
-- url     : https://prove2.me/submissions/76c87185-3a79-47a8-91ff-453647de0d54

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
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
    (hno : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (x : BitString N) (w : Fin (N + G)) (hw : w.val ≠ i.val) :
    c.wireValue x w = c.wireValue (Function.update x i b) w := by
  by_cases h : w.val < N
  · rw [wireValue_lt c x w h, wireValue_lt c _ w h]
    have hne : (⟨w.val, h⟩ : Fin N) ≠ i := fun heq => hw (congrArg Fin.val heq)
    exact (Function.update_of_ne hne b x).symm
  · have hG : w.val - N < G := by omega
    rw [wireValue_ge c x w h, wireValue_ge c _ w h]
    simp only [Gate.eval]
    congr 1; funext k; congr 1
    exact solution c i b hno x _ (hno ⟨w.val - N, hG⟩ k)
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega
end CircuitComplexity.Circuit
