-- Prove2me | solution 1 for CircuitComplexity.ShannonUpper.shannon_construction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:18.599823+00:00
-- url     : https://prove2.me/submissions/f8b340ca-9db7-41c8-ac93-f2e3af67e4d2

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_size_le
public import Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_assembly

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.ShannonUpper
namespace CircuitComplexity.ShannonUpper
theorem _root_.solution (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧ c.size ≤ 18 * 2 ^ N / N := by
  obtain ⟨G, c, heval, hG⟩ := shannon_assembly N hN f
  exact ⟨G, c, heval, by rw [Circuit.size]; exact shannon_size_le N hN G hG⟩
end CircuitComplexity.ShannonUpper
