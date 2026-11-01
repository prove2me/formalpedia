-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_marked_count_cell_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:57:11.250324+00:00
-- url     : https://prove2.me/submissions/aaf65634-8620-4562-a1de-16b95533540b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- A genuine exact-count quadratic bound for a random marked Poisson cell.
Only the count/entire-mark-sequence independence and the L² mark moment enter. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 ν)
    (j : ℕ) :
    (∫ ω in {ω | K ω = j},
      (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) ≤
      μ.real {ω | K ω = j} *
        ((j : ℝ) ^ 2 * ∫ z, f z ^ 2 ∂ν) := by
  have hfSq : Measurable (fun z : E => f z ^ 2) := by fun_prop
  have hfSqI : Integrable (fun z : E => f z ^ 2) ν :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf2
  have hXi (n : ℕ) : MemLp (fun ω => f (Y n ω)) 2 μ := by
    simpa [Function.comp_def] using
      hf2.comp_measurePreserving ((hYL n).measurePreserving (hYm n))
  have hSumLp :
      MemLp (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) 2 μ :=
    memLp_finset_sum (Finset.range j) (fun n hn => hXi n)
  have hSumMeas : Measurable
      (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) := by
    apply Finset.measurable_sum
    intro n hn
    exact hf.comp (hYm n)
  have hLeftI : Integrable
      (fun ω => (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hSumMeas.aestronglyMeasurable).1 hSumLp
  have hSingleSqI (n : ℕ) :
      Integrable (fun ω => f (Y n ω) ^ 2) μ := by
    have hMap : Integrable (fun z => f z ^ 2) (Measure.map (Y n) μ) := by
      rwa [(hYL n).map_eq]
    exact hMap.comp_measurable (hYm n)
  have hRightI : Integrable
      (fun ω => (j : ℝ) * ∑ n ∈ Finset.range j, f (Y n ω) ^ 2) μ := by
    have hSumI : Integrable
        (fun ω => ∑ n ∈ Finset.range j, f (Y n ω) ^ 2) μ :=
      integrable_finsetSum (Finset.range j) (fun n hn => hSingleSqI n)
    exact hSumI.const_mul (j : ℝ)
  have hCellMean :=
    poisson_independent_count_cell_mark_mean_ws01b
      μ ν K Y hKm hYm hYL hIndep j (fun z => f z ^ 2) hfSq hfSqI
  calc
    (∫ ω in {ω | K ω = j},
        (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) ≤
      ∫ ω in {ω | K ω = j},
        (j : ℝ) * ∑ n ∈ Finset.range j, f (Y n ω) ^ 2 ∂μ := by
          apply integral_mono hLeftI.integrableOn hRightI.integrableOn
          intro ω
          simpa only [Finset.card_range] using
            (sq_sum_le_card_mul_sum_sq
              (s := Finset.range j) (f := fun n => f (Y n ω)))
    _ = (j : ℝ) * (∫ ω in {ω | K ω = j},
        ∑ n ∈ Finset.range j, f (Y n ω) ^ 2 ∂μ) := by
          rw [integral_const_mul]
    _ = (j : ℝ) *
          (μ.real {ω | K ω = j} *
            ((j : ℝ) * ∫ z, f z ^ 2 ∂ν)) := by rw [hCellMean]
    _ = μ.real {ω | K ω = j} *
          ((j : ℝ) ^ 2 * ∫ z, f z ^ 2 ∂ν) := by ring
