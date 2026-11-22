-- Prove2me | solution 1 for CircuitComplexity.Circuit.gate_elimination_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:21.138275+00:00
-- url     : https://prove2.me/submissions/a888f3ac-064c-4462-9383-eafae43a75a0

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_essential_inputs_le_mul_size

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (EssentialInputs f).card ≤ k * c.size :=
  essential_inputs_le_mul_size c f hf
end CircuitComplexity.Circuit
