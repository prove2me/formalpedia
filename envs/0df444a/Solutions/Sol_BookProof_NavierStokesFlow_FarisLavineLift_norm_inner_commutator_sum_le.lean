-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:36:54.035201+00:00
-- url     : https://prove2.me/submissions/f0139e21-a658-4e1f-a142-6be1a5a1caa0

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le
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

private theorem parent_comm_sum (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D))
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

theorem solution (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ)
    (hc₂ : 0 ≤ c₂) (v : D)
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k))
    (hbound : ∀ k ∈ s, ‖(inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) :
    ‖(inner ℂ ((v : F))
        ((commDom (∑ k ∈ s, h k) ((∑ k ∈ s, n k) + LinearMap.id) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ).re := by
  classical
  have hid (A B : D →ₗ[ℂ] D) : commDom A (B + LinearMap.id) = commDom A B := by
    simp [commDom, LinearMap.comp_add, LinearMap.add_comp]
  rw [hid, parent_comm_sum s h n hcomm]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, inner_sum, LinearMap.add_apply,
    LinearMap.id_apply, Submodule.coe_add, inner_add_right, Complex.add_re, Complex.re_sum]
  have hv : 0 ≤ (inner ℂ (v : F) (v : F) : ℂ).re := by
    have ht := @norm_sq_eq_re_inner ℂ F _ _ _ (v : F)
    change ‖(v : F)‖ ^ 2 = (inner ℂ (v : F) (v : F) : ℂ).re at ht
    rw [← ht]
    exact sq_nonneg _
  calc
    ‖∑ k ∈ s, (inner ℂ (v : F) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ ∑ k ∈ s, ‖(inner ℂ (v : F) ((commDom (h k) (n k) v : D) : F) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ s, c₂ * (inner ℂ (v : F) ((n k v : D) : F) : ℂ).re := Finset.sum_le_sum hbound
    _ = c₂ * ∑ k ∈ s, (inner ℂ (v : F) ((n k v : D) : F) : ℂ).re := (Finset.mul_sum ..).symm
    _ ≤ c₂ * ((∑ k ∈ s, (inner ℂ (v : F) ((n k v : D) : F) : ℂ).re) + (inner ℂ (v : F) (v : F) : ℂ).re) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) hc₂

#print axioms solution
