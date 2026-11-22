-- Prove2me | solution 1 for CircuitComplexity.or_size_complexity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:19.158117+00:00
-- url     : https://prove2.me/submissions/028fdaae-f7f0-44a9-9394-04bc9f6f8059

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
public import Theorems.Thm_CircuitComplexity_ShannonUpper_binopCircuit_or_correct


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution [CompleteBasis Basis.andOr2] [NeZero N]
    (g₁ g₂ : BitString N → Bool) :
    Circuit.sizeComplexity Basis.andOr2 (fun x => g₁ x || g₂ x) ≤
      Circuit.sizeComplexity Basis.andOr2 g₁ +
      Circuit.sizeComplexity Basis.andOr2 g₂ + 1 := by
  obtain ⟨G₁, c₁, hsize₁, heval₁⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) g₁
  obtain ⟨G₂, c₂, hsize₂, heval₂⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) g₂
  let c := ShannonUpper.binopCircuit AONOp.or c₁ c₂
  have hcorrect : (fun x => (c.eval x) 0) = fun x => g₁ x || g₂ x :=
    ShannonUpper.binopCircuit_or_correct c₁ c₂ g₁ g₂ heval₁ heval₂
  calc Circuit.sizeComplexity Basis.andOr2 (fun x => g₁ x || g₂ x)
      ≤ c.size := Circuit.size_complexity_le c _ hcorrect
    _ = (G₁ + G₂ + 2) + 1 := rfl
    _ = Circuit.sizeComplexity Basis.andOr2 g₁ +
        Circuit.sizeComplexity Basis.andOr2 g₂ + 1 := by
        rw [← hsize₁, ← hsize₂]
        unfold Circuit.size
        omega
end CircuitComplexity
