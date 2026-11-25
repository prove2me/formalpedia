-- Prove2me | solution 1 for ErdosPosa.erdos_posa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:44:04.173877+00:00
-- url     : https://prove2.me/submissions/a79be006-865d-42c2-82de-7f2ef1c16859

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMain
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Theorems.Thm_ErdosPosa_erdos_posa_bound_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
universe u
namespace ErdosPosa
theorem _root_.solution : ∃ f : ℕ → ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨ ∃ X : Set V, X.ncard ≤ f k ∧ IsFeedbackSet G X :=
  ⟨fun k => 65 * (k + 1) * (Nat.log 2 (k + 1) + 1), fun k _ _ G => erdos_posa_bound_aux k G⟩
end ErdosPosa
