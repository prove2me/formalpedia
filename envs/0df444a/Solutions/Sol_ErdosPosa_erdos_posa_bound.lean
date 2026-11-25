-- Prove2me | solution 1 for ErdosPosa.erdos_posa_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:44:06.953545+00:00
-- url     : https://prove2.me/submissions/7221b97d-4685-445f-ba35-acd5311ade89

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
theorem _root_.solution : ∃ c : ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨
      ∃ X : Set V, X.ncard ≤ c * (k + 1) * (Nat.log 2 (k + 1) + 1) ∧ IsFeedbackSet G X :=
  ⟨65, fun k _ _ G => erdos_posa_bound_aux k G⟩
end ErdosPosa
