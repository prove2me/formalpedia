-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:15:53.348184+00:00
-- url     : https://prove2.me/submissions/9b242322-c8b2-43b1-8934-de8344ab28c3

import Mathlib
import Theorems.Thm_ProbabilityTheory_integral_abs_le_sqrt_integral_sq
open MeasureTheory Set Filter Topology
noncomputable section

/-- A genuine finite physical grid with integrable cross-products has a
square-integrable full sum; its L1 norm is bounded by the square-root
of the proven total L2 energy, with no cross-cell independence assumed. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (Z : ℕ → Ω → ℝ)
    (hZM : ∀ i ∈ Finset.range m, Measurable (Z i))
    (hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (B : ℝ)
    (hBudget :
      (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤ B) :
    (∫ ω, |∑ i ∈ Finset.range m, Z i ω| ∂P) ≤
      Real.sqrt B := by
  have hMeas : Measurable
      (fun ω => ∑ i ∈ Finset.range m, Z i ω) := by
    apply Finset.measurable_sum
    intro i hi
    exact hZM i hi
  have hSquare : Integrable
      (fun ω => (∑ i ∈ Finset.range m, Z i ω)^2) P := by
    have hDouble : Integrable
        (fun ω => ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range m, Z i ω * Z j ω) P := by
      apply integrable_finset_sum
      intro i hi
      apply integrable_finset_sum
      intro j hj
      exact hPair i hi j hj
    convert hDouble using 1
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
  exact (ProbabilityTheory.integral_abs_le_sqrt_integral_sq
    P (fun ω => ∑ i ∈ Finset.range m, Z i ω)
    hMeas hSquare).trans (Real.sqrt_le_sqrt hBudget)
