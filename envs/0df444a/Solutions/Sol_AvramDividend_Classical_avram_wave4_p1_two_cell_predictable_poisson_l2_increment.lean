-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_two_cell_predictable_poisson_l2_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:16:29.93999+00:00
-- url     : https://prove2.me/submissions/27b73c73-2148-4465-bf19-6728d9cd509b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_past_weighted_poisson_count_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_future_poisson_past_product_orthogonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

/-- One genuine predictable Poisson-count cell increases the L² energy of
a preceding square-integrable past payoff by rate times the squared weight.
Only joint independence from the current future count is required. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H J : Ω → ℝ)
    (hH2 : MemLp H 2 P) (hHSq : Integrable (fun ω => H ω ^ 2) P)
    (hJm : Measurable J) (hJ2 : MemLp J 2 P)
    (hJSq : Integrable (fun ω => J ω ^ 2) P)
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hKInt : Integrable (fun ω => (K ω : ℝ) - (r : ℝ)) P)
    (hJointPast : IndepFun (fun ω => (H ω, J ω)) K P) :
    Integrable (fun ω => (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) P ∧
      (∫ ω, (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
        (∫ ω, H ω ^ 2 ∂P) + (r : ℝ) * ∫ ω, J ω ^ 2 ∂P := by
  have hIndepJ : IndepFun J K P := by
    simpa [Function.comp_def] using
      hJointPast.comp
        (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2))
        (by fun_prop : Measurable (fun n : ℕ => n))
  have hNext := AvramDividend.Classical.avram_wave4_p1_past_weighted_poisson_count_l2_isometry
    P J hJm hJSq K hKm r hKlaw hIndepJ
  have hCross := AvramDividend.Classical.avram_wave4_p1_future_poisson_past_product_orthogonal
    P H J hH2 hJ2 K hKm r hKlaw hKInt hJointPast
  have hDouble : Integrable
      (fun ω => (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ)))) P := by
    exact hCross.1.const_mul 2
  have hPoint :
      (fun ω => (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) =
      ((fun ω => H ω ^ 2) +
        (fun ω => (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2)) +
        (fun ω => (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ)))) := by
    funext ω
    dsimp
    ring
  constructor
  · rw [hPoint]
    exact (hHSq.add hNext.1).add hDouble
  · have hIntegralExpand :
        (∫ ω, (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
          (∫ ω, (H ω ^ 2 +
              (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) +
              (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) ∂P) := by
      have hEq :
          (fun ω => (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) =
            (fun ω => (H ω ^ 2 +
              (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) +
              (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ)))) := by
        funext ω
        ring
      rw [hEq]
    have hSplitOuter :
        (∫ ω, (H ω ^ 2 +
          (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) +
          (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) ∂P) =
        (∫ ω, H ω ^ 2 +
          (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) +
        (∫ ω, (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add (hHSq.add hNext.1) hDouble)
    have hSplitInner :
        (∫ ω, H ω ^ 2 +
          (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
        (∫ ω, H ω ^ 2 ∂P) +
        (∫ ω, (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) := by
      simpa only [Pi.add_apply] using (integral_add hHSq hNext.1)
    have hScale :
        (∫ ω, (2 : ℝ) * ((H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) ∂P) =
          (2 : ℝ) * (∫ ω, (H ω * J ω) * ((K ω : ℝ) - (r : ℝ)) ∂P) := by
      simp only [integral_const_mul]
    calc
      (∫ ω, (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
          (∫ ω, H ω ^ 2 ∂P) +
            (∫ ω, (J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) +
            (2 : ℝ) * (∫ ω, (H ω * J ω) * ((K ω : ℝ) - (r : ℝ)) ∂P) := by
              rw [hIntegralExpand, hSplitOuter, hSplitInner, hScale]
      _ = (∫ ω, H ω ^ 2 ∂P) +
            (r : ℝ) * ∫ ω, J ω ^ 2 ∂P := by
              rw [hNext.2, hCross.2]
              ring
