-- Prove2me | solution 1 for CircuitComplexity.shannon_lower_bound_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:59.463185+00:00
-- url     : https://prove2.me/submissions/63beba83-d09d-419b-97ad-90607194c46d

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Theorems.Thm_CircuitComplexity_circuit_eval_eq_evalD
public import Theorems.Thm_CircuitComplexity_evalD_padDesc
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_shannon_lower_bound
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N : Nat) [NeZero N] (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ G (c : Circuit Basis.andOr2 N 1 G),
        G + 1 ≤ 2 ^ N / (5 * N) →
        (fun x => (c.eval x) 0) ≠ f := by
  obtain ⟨f, hf⟩ := shannon_lower_bound N hN
  exact ⟨f, fun G c hsize habs => by
    have hspos := s_pos N hN
    have hG1 : 0 < G + 1 := Nat.succ_pos G
    let d := circuitToDesc c
    let d' := padDesc d (2 ^ N / (5 * N)) hG1 hsize
    have h1 : evalD hspos d' = evalD hG1 d := evalD_padDesc d hG1 hsize hspos
    have h2 : (fun x => (c.eval x) 0) = evalD hG1 d := circuit_eval_eq_evalD c
    simp_all⟩
end CircuitComplexity
