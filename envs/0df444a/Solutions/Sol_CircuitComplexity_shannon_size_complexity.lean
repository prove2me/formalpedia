-- Prove2me | solution 1 for CircuitComplexity.shannon_size_complexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:36.269071+00:00
-- url     : https://prove2.me/submissions/d03265f9-162a-4612-8d11-a1ded445494d

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Theorems.Thm_CircuitComplexity_Circuit_size_complexity_witness
public import Theorems.Thm_CircuitComplexity_shannon_lower_bound_circuit


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N : Nat) [NeZero N] (hN : 6 ≤ N)
    [CompleteBasis Basis.andOr2] :
    ∃ f : BitString N → Bool,
      Circuit.sizeComplexity Basis.andOr2 f > 2 ^ N / (5 * N) := by
  obtain ⟨f, hf⟩ := shannon_lower_bound_circuit N hN
  refine ⟨f, ?_⟩
  by_contra hle; push Not at hle
  obtain ⟨G, c, hs, hc⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) f
  have : c.size ≤ 2 ^ N / (5 * N) := hs ▸ hle
  exact hf G c (by rw [Circuit.size] at this; omega) hc
end CircuitComplexity
