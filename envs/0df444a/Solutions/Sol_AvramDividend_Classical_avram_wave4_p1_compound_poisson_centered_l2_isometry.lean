-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_compound_poisson_centered_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:58:17.778018+00:00
-- url     : https://prove2.me/submissions/d56f20b5-6e9f-4e0b-bf46-78f8d56db8c8

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_random_mark_sum_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_campbell_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- The compensated iid marked Poisson sum has exactly r times the mark variance intensity. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    (∫ ω, ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν) ^ 2 ∂μ) =
      (r : ℝ) * ∫ z, f z ^ 2 ∂ν := by
  let S : Ω → ℝ := fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)
  let c : ℝ := (r : ℝ) * ∫ z, f z ∂ν
  have hS : Integrable S μ :=
    poisson_random_mark_sum_integrable_ws01b
      μ ν K Y hKm r hKlaw hYm hYL hIndep f hf hfI
  have hS2 : Integrable (fun ω => S ω ^ 2) μ :=
    avram_wave4_p1_poisson_random_mark_sum_square_integrable
      μ ν K Y hKm r hKlaw hYm hYL hIndep f hf hf2
  have hcS : Integrable (fun ω => (2 * c) * S ω) μ :=
    hS.const_mul (2 * c)
  have hId : (∫ ω, (S ω - c) ^ 2 ∂μ) =
      (∫ ω, S ω ^ 2 ∂μ) - (2 * c) * (∫ ω, S ω ∂μ) + c ^ 2 := by
    calc
      (∫ ω, (S ω - c) ^ 2 ∂μ) =
          ∫ ω, (S ω ^ 2 - (2 * c) * S ω) + c ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = (∫ ω, S ω ^ 2 ∂μ) - (2 * c) * (∫ ω, S ω ∂μ) + c ^ 2 := by
        have hAdd : (∫ ω, (S ω ^ 2 - (2 * c) * S ω) + c ^ 2 ∂μ) =
            (∫ ω, S ω ^ 2 - (2 * c) * S ω ∂μ) +
              (∫ ω, c ^ 2 ∂μ) := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_add (hS2.sub hcS) (integrable_const (c ^ 2))
        have hSub : (∫ ω, S ω ^ 2 - (2 * c) * S ω ∂μ) =
            (∫ ω, S ω ^ 2 ∂μ) - (∫ ω, (2 * c) * S ω ∂μ) := by
          simpa only [Pi.sub_apply] using integral_sub hS2 hcS
        rw [hAdd, hSub, integral_const_mul]
        simp
  have hMean : (∫ ω, S ω ∂μ) = c :=
    poisson_random_mark_sum_campbell_ws01b
      μ ν K Y hKm r hKlaw hYm hYL hIndep f hf hfI
  have hSecond : (∫ ω, S ω ^ 2 ∂μ) =
      (r : ℝ) * (∫ z, f z ^ 2 ∂ν) +
        (r : ℝ) ^ 2 * (∫ z, f z ∂ν) ^ 2 :=
    avram_wave4_p1_random_mark_sum_exact_second_moment
      μ ν K Y hKm r hKlaw hYm hYL hYi hIndep f hf hfI hf2
  change (∫ ω, (S ω - c) ^ 2 ∂μ) = _
  rw [hId, hMean, hSecond]
  dsimp [c]
  ring