-- Prove2me | solution 1 for FamousTheorems.lagrange_multiplier_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:56:18.020335+00:00
-- url     : https://prove2.me/submissions/5cfe823a-8d43-482f-9ac7-96470b0b2837

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {φ : E → ℝ} {x₀ : E}
    {φ' : StrongDual ℝ E} {ι : Type*} [Fintype ι] {f : ι → E → ℝ} {f' : ι → StrongDual ℝ E}
    (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀) (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∑ i, Λ i • f' i + Λ₀ • φ' = 0 :=
  hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ'
