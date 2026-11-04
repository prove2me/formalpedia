-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:49:33.208428+00:00
-- url     : https://prove2.me/submissions/d589e222-00cc-4e28-add4-c71929484c36

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Finite predictable-step isometry algebra: pairwise orthogonal actual-space
L² increments have additive second moments. Their orthogonality remains
an explicit original-source stochastic hypothesis. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ι) (F : ι → Ω → ℝ)
    (hProd : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω => F i ω * F j ω) P)
    (hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ S, F i ω)^2 ∂P) =
      ∑ i ∈ S, ∫ ω, (F i ω)^2 ∂P := by
  classical
  have hInner : ∀ i ∈ S,
      Integrable (fun ω => ∑ j ∈ S, F i ω * F j ω) P := by
    intro i hi
    exact integrable_finset_sum S (hProd i hi)
  calc
    (∫ ω, (∑ i ∈ S, F i ω)^2 ∂P) =
        ∫ ω, ∑ i ∈ S, ∑ j ∈ S, F i ω * F j ω ∂P := by
      congr 1
      funext ω
      simp only [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ S, ∑ j ∈ S, ∫ ω, F i ω * F j ω ∂P := by
      rw [integral_finset_sum S hInner]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum S (hProd i hi)]
    _ = ∑ i ∈ S, ∫ ω, (F i ω)^2 ∂P := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j hj hji
        exact hOrth i hi j hj (Ne.symm hji)
      · intro hiNot
        exact False.elim (hiNot hi)