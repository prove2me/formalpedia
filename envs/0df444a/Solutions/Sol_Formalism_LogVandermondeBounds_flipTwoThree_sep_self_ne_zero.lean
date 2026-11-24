-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.sep_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:40.31501+00:00
-- url     : https://prove2.me/submissions/28fefe7b-e85d-4190-900e-aa548596eb8b

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_mem_Iset_of
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_Iset_disj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    sep lam nu nu ≠ 0 := by
  unfold sep
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro y hy
  rw [Finset.mem_erase] at hy
  unfold ev
  rw [Finset.prod_ne_zero_iff]
  intro j _ h0
  by_cases hij : i = j
  · subst hij
    exact hy.1 (by linarith)
  · have hyj : y - (i : ℤ) = nu j - (j : ℤ) := by linarith
    have m1 : y - (i : ℤ) ∈ (Iset lam (B0 lam nu) i).image (fun y => y - (i : ℤ)) :=
      Finset.mem_image_of_mem _ hy.2
    have m2 : y - (i : ℤ) ∈ (Iset lam (B0 lam nu) j).image (fun y => y - (j : ℤ)) := by
      rw [hyj]
      exact Finset.mem_image_of_mem _ (mem_Iset_of h rfl j)
    exact Finset.disjoint_left.mp (Iset_disj h.1 _ i j hij) m1 m2
end Formalism.LogVandermondeBounds.flipTwoThree
