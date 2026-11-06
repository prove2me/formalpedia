-- Prove2me | solution 1 for BookProof.HermiteLadder.apply_sum_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:29:36.776198+00:00
-- url     : https://prove2.me/submissions/db1bf4de-b9d9-41dd-aadd-d20dd5cb8931

import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

theorem solution (v : ι → E) (σ : ι → ι) (s : ι → ℂ) {D : Submodule ℂ E}
    (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = s a • v (σ a))
    (S : Finset ι) (f : ι → ℂ) :
    ∀ hu : (∑ a ∈ S, f a • v a) ∈ D,
      T ⟨∑ a ∈ S, f a • v a, hu⟩ = ∑ a ∈ S, (f a * s a) • v (σ a) := by
  intro hu
  have hrepr : (⟨∑ a ∈ S, f a • v a, hu⟩ : D) =
      ∑ a ∈ S, f a • (⟨v a, hvD a⟩ : D) := by
    ext
    simp
  rw [hrepr]
  simp only [map_sum, map_smul, hT, mul_smul]
