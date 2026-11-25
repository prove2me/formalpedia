-- Prove2me | solution 1 for BayesianPersuasion.Proof.sum_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:22.648496+00:00
-- url     : https://prove2.me/submissions/2eddd1e1-b363-407e-a6c1-7575981498e5

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_CompactHull

set_option autoImplicit true
@[expose] public section
public section
open Set Finset
open BayesianPersuasion BayesianPersuasion.Proof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
namespace BayesianPersuasion.Proof
theorem _root_.solution {k N : ℕ} (hk : k ≤ N) {G : Type*} [AddCommMonoid G]
    (f : Fin k → G) :
    (∑ j : Fin N, if h : j.val < k then f ⟨j.val, h⟩ else 0) = ∑ j, f j := by
  classical
  symm
  refine @Finset.sum_of_injOn (Fin k) (Fin N) G _ univ univ f
    (fun j => if h : j.val < k then f ⟨j.val, h⟩ else 0)
    (fun j : Fin k => (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro j₁ _ j₂ _ h; exact Fin.ext (Fin.mk.inj h)
  · intro _ _; simp
  · intro j _ hj
    have h : ¬ (j.val < k) := by
      intro hlt; apply hj; exact ⟨⟨j.val, hlt⟩, by simp, Fin.ext rfl⟩
    exact dif_neg h
  · intro j _; simp only [dif_pos j.isLt]
end BayesianPersuasion.Proof
