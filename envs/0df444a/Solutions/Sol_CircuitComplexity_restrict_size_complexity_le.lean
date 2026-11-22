-- Prove2me | solution 1 for CircuitComplexity.restrict_size_complexity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:39.955797+00:00
-- url     : https://prove2.me/submissions/faa7e396-0883-489e-894f-01a1966f1de2

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism
public import Theorems.Thm_CircuitComplexity_Circuit_size_complexity_le
public import Theorems.Thm_CircuitComplexity_Circuit_size_complexity_witness
public import Theorems.Thm_CircuitComplexity_restrictCircuit_eval


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution [CompleteBasis Basis.andOr2] [NeZero m]
    (f : BitString ((k + 1) + m) → Bool) (b : Bool) :
    Circuit.sizeComplexity Basis.andOr2 (restrictFirst f b) ≤
      Circuit.sizeComplexity Basis.andOr2 f := by
  obtain ⟨G, c, hsize, heval⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) f
  calc Circuit.sizeComplexity Basis.andOr2 (restrictFirst f b)
      ≤ (restrictCircuit (k := k) b c).size :=
        Circuit.size_complexity_le _ _ (restrictCircuit_eval b c f heval)
    _ = c.size := rfl
    _ = Circuit.sizeComplexity Basis.andOr2 f := hsize
end CircuitComplexity
