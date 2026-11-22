-- Prove2me | solution 1 for CircuitComplexity.Circuit.card_coveredInputs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:48.928798+00:00
-- url     : https://prove2.me/submissions/61d65fe9-bee5-4f57-a752-509949d682b9

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_mem_coveredInputs
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution (g : Gate B (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ g.fanIn := by
  suffices coveredInputs g ⊆
      (Finset.univ : Finset (Fin g.fanIn)).image
        (fun k => if h : (g.inputs k).val < N
          then ⟨(g.inputs k).val, h⟩
          else ⟨0, NeZero.pos N⟩) by
    calc (coveredInputs g).card
        ≤ _ := Finset.card_le_card this
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = g.fanIn := by simp
  intro i hi
  rw [mem_coveredInputs] at hi
  obtain ⟨k, hk⟩ := hi
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨k, by simp [hk]⟩
end CircuitComplexity.Circuit
