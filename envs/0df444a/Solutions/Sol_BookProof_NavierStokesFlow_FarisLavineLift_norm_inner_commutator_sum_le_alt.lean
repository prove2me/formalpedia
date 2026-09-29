-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le_alt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:06:10.518756+00:00
-- url     : https://prove2.me/submissions/b555bd4e-f3e6-4d2f-a4d0-ea5fb277600d

-- Generated from ChapterNavierStokesFarisLavineLift.lean — solution of BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le'
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_inner_commutator_sum_le
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift











open FullEsa



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)











open LpNat DiagonalEsa









variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ)
    (hc₂ : 0 ≤ c₂) (v : D)
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k))
    (hbound : ∀ k ∈ s, ‖(inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) :
    ‖(inner ℂ ((v : F))
        ((commDom (∑ k ∈ s, h k) ((∑ k ∈ s, n k) + LinearMap.id) v : D) : F) : ℂ)‖
      ≤ c₂ * ‖(inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ)‖ := by

  refine le_trans (norm_inner_commutator_sum_le s h n c₂ hc₂ v hcomm hbound) ?_
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hc₂
