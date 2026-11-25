-- Prove2me | solution 1 for CyclePacking.erdos_posa_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:47:32.823045+00:00
-- url     : https://prove2.me/submissions/fc277dc6-b553-4222-84bc-560185d08c82

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Definitions.Def_ErdosPosaCycles_Solution
public import Theorems.Thm_ErdosPosa_erdos_posa_bound


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CyclePacking
universe u
namespace CyclePacking
theorem _root_.solution : ∃ c : ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨
      ∃ X : Set V, X.ncard ≤ c * (k + 1) * (Nat.log 2 (k + 1) + 1) ∧ IsFeedbackSet G X :=
  ErdosPosa.erdos_posa_bound
end CyclePacking
