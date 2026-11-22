-- Prove2me | solution 1 for CircuitComplexity.shannon_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:57.175834+00:00
-- url     : https://prove2.me/submissions/947ee6e8-5cfd-4fa5-97eb-d9d5aa785660

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
public import Theorems.Thm_CircuitComplexity_Circuit_size_complexity_le
public import Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_construction


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution
    (N : Nat) (hN : 16 ≤ N) [NeZero N]
    (f : BitString N → Bool) :
    Circuit.sizeComplexity Basis.andOr2 f ≤ 18 * 2 ^ N / N := by
  obtain ⟨G, c, heval, hsize⟩ := ShannonUpper.shannon_construction N hN f
  exact le_trans (Circuit.size_complexity_le c f heval) hsize
end CircuitComplexity
