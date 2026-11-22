-- Prove2me | solution 1 for CircuitComplexity.schnorr_size_complexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:37.241367+00:00
-- url     : https://prove2.me/submissions/09a85bfd-784f-4116-9446-6668c8006a2d

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Schnorr
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_size_complexity_witness
public import Theorems.Thm_CircuitComplexity_schnorr_lower_bound_circuit
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N : Nat) [NeZero N] (hN : 1 ≤ N)
    [CompleteBasis Basis.andOr2] :
    Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1 := by
  by_contra hlt; push Not at hlt
  obtain ⟨G, c, hs, hc⟩ := Circuit.size_complexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  have hbound := schnorr_lower_bound_circuit N G c false heval hN
  rw [Circuit.size] at hs; omega
end CircuitComplexity
