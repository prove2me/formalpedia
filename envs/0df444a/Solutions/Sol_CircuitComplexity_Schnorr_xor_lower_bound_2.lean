-- Prove2me | solution 1 for CircuitComplexity.Schnorr.xor_lower_bound_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:24.628638+00:00
-- url     : https://prove2.me/submissions/ab6ac27e-d7b9-4310-a459-dd8da41eca12

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Theorems.Thm_CircuitComplexity_Schnorr_restriction_eliminates_two
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Schnorr_xorBool_flip
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace Schnorr
private theorem xor_circuit_essential {N s : Nat} (d : CircDesc N s) (hs : 0 < s)
    (comp : Bool) (heval : ∀ x, evalD hs d x = comp.xor (xorBool N x))
    (a : Fin N) (x : BitString N) :
    evalD hs d x ≠ evalD hs d (Function.update x a (!x a)) := by
  rw [heval, heval, xorBool_flip]
  cases comp <;> cases xorBool N x <;> simp [Bool.xor]
end Schnorr
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution (N s : Nat) (hs : 0 < s) (d : CircDesc N s) (comp : Bool)
    (heval : ∀ x, evalD hs d x = comp.xor (xorBool N x))
    (hN : 1 ≤ N) : s + 1 ≥ 2 * N := by
  induction N generalizing s comp with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; omega
    -- n ≥ 1, so N = n+1 ≥ 2. Need s ≥ 2n+1.
    -- Every input is essential
    have hessential := xor_circuit_essential d hs comp heval
    -- Restrict one input + eliminate 2 gates → smaller circuit for XOR_n
    obtain ⟨s', d', hs', comp', hsize, heval'⟩ :=
      restriction_eliminates_two d hs (by omega) comp heval hessential
    have := ih s' hs' d' comp' heval' (by omega)
    omega
end CircuitComplexity.Schnorr
