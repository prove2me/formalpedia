-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.commDom_sum
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:17:03.175683+00:00
-- url     : https://prove2.me/submissions/0c87729f-04b3-4114-ae7b-8916adb3202e

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.commDom_sum
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D))
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k)) :
    commDom (∑ k ∈ s, h k) (∑ k ∈ s, n k) = ∑ k ∈ s, commDom (h k) (n k) := by
  have heq : commDom (∑ k ∈ s, h k) (∑ k ∈ s, n k) =
      ∑ k ∈ s, ∑ l ∈ s, commDom (h k) (n l) := by
    ext x
    simp only [commDom, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun k l => (h l) ((n k) x))]
  rw [heq]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_eq_single k
  · intro l hl hne
    exact sub_eq_zero.mpr (hcomm k hk l hl hne.symm)
  · intro hnot
    exact (hnot hk).elim
#print axioms solution
