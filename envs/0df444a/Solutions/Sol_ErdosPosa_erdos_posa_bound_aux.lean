-- Prove2me | solution 1 for ErdosPosa.erdos_posa_bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:42:53.289912+00:00
-- url     : https://prove2.me/submissions/8458656d-8ceb-4453-9ce0-9498e5e772a5

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMain
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Theorems.Thm_ErdosPosa_not_isAcyclic_induce_iff
public import Theorems.Thm_ErdosPosa_reduction


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
universe u
namespace ErdosPosa
theorem _root_.solution (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V) :
    HasDisjointCycles G k ∨
      ∃ X : Set V, X.ncard ≤ 65 * (k + 1) * (Nat.log 2 (k + 1) + 1) ∧ IsFeedbackSet G X := by
  cases k with
  | zero => exact Or.inl ⟨Fin.elim0, fun i _ _ => i.elim0, fun i => i.elim0⟩
  | succ j =>
    rcases reduction G j with ⟨F, hF, hFc⟩ | ⟨X, hX, hXc⟩
    · exact Or.inl ⟨F, hF, fun i => not_isAcyclic_induce_iff.2 (hFc i)⟩
    · refine Or.inr ⟨X, hX.trans ?_, ?_⟩
      · unfold gEP
        have hl : Nat.log 2 (j + 1) ≤ Nat.log 2 (j + 1 + 1) := Nat.log_mono_right (by omega)
        nlinarith
      · by_contra h
        exact hXc (not_isAcyclic_induce_iff.1 h)
end ErdosPosa
