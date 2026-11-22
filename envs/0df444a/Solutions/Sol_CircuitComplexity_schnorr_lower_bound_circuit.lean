-- Prove2me | solution 1 for CircuitComplexity.schnorr_lower_bound_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:01.316919+00:00
-- url     : https://prove2.me/submissions/abf084db-246c-4f22-b34a-dda634a8a288

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
public import Theorems.Thm_CircuitComplexity_Schnorr_xor_lower_bound_2


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x))
    (hN : 1 ≤ N) : G + 2 ≥ 2 * N := by
  have hG1 : 0 < G + 1 := Nat.succ_pos G
  have h := circuit_eval_eq_evalD c
  have heval' : ∀ x, evalD hG1 (circuitToDesc c) x = comp.xor (Schnorr.xorBool N x) :=
    fun x => (congr_fun h x).symm ▸ heval x
  exact Schnorr.xor_lower_bound_2 N (G + 1) hG1 (circuitToDesc c) comp heval' hN
end CircuitComplexity
