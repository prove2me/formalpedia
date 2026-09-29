-- Prove2me | solution 1 for BookProof.HermiteRelative.apply_sum_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:58:57.17469+00:00
-- url     : https://prove2.me/submissions/d13acf04-af88-44aa-923f-6119d1897cb9

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.apply_sum_of_diagonal
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (v : ι → E) (lam : ι → ℝ) {D : Submodule ℂ E}
    (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (s : Finset ι) (f : ι → ℂ) :
    ∀ hu : (∑ a ∈ s, f a • v a) ∈ D,
      T ⟨∑ a ∈ s, f a • v a, hu⟩ = ∑ a ∈ s, (((lam a : ℝ) : ℂ) * f a) • v a := by

  classical
  induction s using Finset.induction with
  | empty =>
      intro hu
      have h0 : (⟨∑ a ∈ (∅ : Finset ι), f a • v a, hu⟩ : D) = 0 := Subtype.ext (by simp)
      rw [h0, map_zero, Finset.sum_empty]
  | insert a s ha ih =>
      intro hu
      have hva : f a • v a ∈ D := Submodule.smul_mem _ _ (hvD a)
      have hs : (∑ b ∈ s, f b • v b) ∈ D :=
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvD b)
      have hsplit : (⟨∑ b ∈ insert a s, f b • v b, hu⟩ : D)
          = ⟨f a • v a, hva⟩ + ⟨∑ b ∈ s, f b • v b, hs⟩ := by
        apply Subtype.ext
        simpa using Finset.sum_insert ha
      have hsm : (⟨f a • v a, hva⟩ : D) = f a • ⟨v a, hvD a⟩ := Subtype.ext rfl
      rw [hsplit, map_add, hsm, map_smul, hT a (hvD a), ih hs, Finset.sum_insert ha, smul_smul,
        mul_comm (f a)]
