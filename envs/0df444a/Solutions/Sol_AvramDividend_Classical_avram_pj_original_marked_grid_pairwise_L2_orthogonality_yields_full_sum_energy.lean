-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:52:57.83221+00:00
-- url     : https://prove2.me/submissions/428707ad-c30f-4fa9-8f71-2746c903d746

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set
noncomputable section

/-- Exact diagonal second-moment identity for a finite original
stopped marked-grid sum when its distinct cells are orthogonal. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ℕ) (Z : ℕ → Ω → ℝ)
    (hPair : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hCross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ ω, Z i ω * Z j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∑ i ∈ s, ∫ ω, (Z i ω)^2 ∂P := by
  have hExpand (ω : Ω) :
      (∑ i ∈ s, Z i ω)^2 =
        ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hExpand]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum]
    · calc
      (∑ j ∈ s, ∫ ω, Z i ω * Z j ω ∂P) =
          ∑ j ∈ s, if j = i then
            ∫ ω, Z i ω * Z i ω ∂P else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji, hCross i hi j hj (Ne.symm hji)]
      _ = ∫ ω, (Z i ω)^2 ∂P := by
        simp [hi, pow_two]
    · intro j hj
      exact hPair i hi j hj
  · intro i hi
    exact integrable_finset_sum s (fun j hj => hPair i hi j hj)
