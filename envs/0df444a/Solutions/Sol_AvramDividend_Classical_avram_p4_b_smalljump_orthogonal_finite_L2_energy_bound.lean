-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:51:50.861686+00:00
-- url     : https://prove2.me/submissions/078658b3-5878-4c26-9629-9670bd595e81

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Finite orthogonal jump-step second moments are controlled by the sum of
the genuine cell energy bounds. The stochastic covariance and diagonal
bounds are explicit source hypotheses. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ι) (F : ι → Ω → ℝ) (v : ι → ℝ)
    (hProd : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω => F i ω * F j ω) P)
    (hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0)
    (hVar : ∀ i ∈ S,
      (∫ ω, (F i ω)^2 ∂P) ≤ v i) :
    (∫ ω, (∑ i ∈ S, F i ω)^2 ∂P) ≤ ∑ i ∈ S, v i := by
  rw [AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
    S F hProd hOrth]
  exact Finset.sum_le_sum hVar