-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.group_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:39.207456+00:00
-- url     : https://prove2.me/submissions/9511f491-6daa-4474-98bb-76a258534a5f

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution {A : Type*} [AddCommMonoid A] (t R : ℕ) (r : Fin R)
    (f : Fin (2 * t * R) → A) :
    (∑ b ∈ Finset.univ.filter (fun b => group t R b = r), f b) =
      ∑ j : Fin (2 * t), f ((indexEquiv t R).symm (r, j)) := by
  classical
  apply Finset.sum_bij (fun b _ => (indexEquiv t R b).2)
  · intro b hb
    exact Finset.mem_univ _
  · intro a ha b hb hab
    apply (indexEquiv t R).injective
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  · intro j hj
    refine ⟨(indexEquiv t R).symm (r, j), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (indexEquiv t R ((indexEquiv t R).symm (r, j))).1 = r
      rw [Equiv.apply_symm_apply]
    · simp
  · intro b hb
    apply congrArg f
    apply (indexEquiv t R).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (Finset.mem_filter.mp hb).2 rfl
end DeletionCode.CanonicalIndex
