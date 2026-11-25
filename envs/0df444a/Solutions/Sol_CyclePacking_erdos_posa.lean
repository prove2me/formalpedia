-- Prove2me | solution 1 for CyclePacking.erdos_posa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:47:09.97249+00:00
-- url     : https://prove2.me/submissions/4cf4f851-40ff-4f42-aea3-0e4570efcd11

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Definitions.Def_ErdosPosaCycles_Solution
public import Theorems.Thm_ErdosPosa_erdos_posa


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CyclePacking
universe u
namespace CyclePacking
theorem _root_.solution : ∃ f : ℕ → ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨ ∃ X : Set V, X.ncard ≤ f k ∧ IsFeedbackSet G X :=
  ErdosPosa.erdos_posa
end CyclePacking
