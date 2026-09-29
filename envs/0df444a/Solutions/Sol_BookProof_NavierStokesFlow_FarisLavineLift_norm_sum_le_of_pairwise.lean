-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:37:52.364774+00:00
-- url     : https://prove2.me/submissions/eccd46c0-4c7f-4852-9908-87f8f67835fc

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (cst : ℝ)
    (hc : 0 ≤ cst) (v : D)
    (hpair : ∀ k ∈ s, ∀ l ∈ s,
      |(inner ℂ ((h k v : D) : F) ((h l v : D) : F) : ℂ).re|
        ≤ cst ^ 2 * (inner ℂ ((n k v : D) : F) ((n l v : D) : F) : ℂ).re) :
    ‖(((∑ k ∈ s, h k) v : D) : F)‖ ≤ cst * ‖(((∑ k ∈ s, n k) v : D) : F)‖ := by
  classical
  have hsquare (a : κ → (D →ₗ[ℂ] D)) :
      ‖(((∑ k ∈ s, a k) v : D) : F)‖ ^ 2 =
        ∑ k ∈ s, ∑ l ∈ s, (inner ℂ ((a k v : D) : F) ((a l v : D) : F) : ℂ).re := by
    have ht : ‖(((∑ k ∈ s, a k) v : D) : F)‖ ^ 2 =
        (inner ℂ (((∑ k ∈ s, a k) v : D) : F) (((∑ k ∈ s, a k) v : D) : F) : ℂ).re :=
      @norm_sq_eq_re_inner ℂ F _ _ _ _
    rw [ht]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, inner_sum, sum_inner, Complex.re_sum]
    exact Finset.sum_comm
  have hs : ‖(((∑ k ∈ s, h k) v : D) : F)‖ ^ 2 ≤
      cst ^ 2 * ‖(((∑ k ∈ s, n k) v : D) : F)‖ ^ 2 := by
    rw [hsquare, hsquare]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro l hl
    exact (le_abs_self _).trans (hpair k hk l hl)
  have hcprod : 0 ≤ cst * ‖(((∑ k ∈ s, n k) v : D) : F)‖ := mul_nonneg hc (norm_nonneg _)
  nlinarith [norm_nonneg ((((∑ k ∈ s, h k) v : D) : F))]

#print axioms solution
