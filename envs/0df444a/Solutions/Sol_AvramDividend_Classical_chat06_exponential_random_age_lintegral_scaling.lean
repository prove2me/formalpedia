-- Prove2me | solution 1 for AvramDividend.Classical.chat06_exponential_random_age_lintegral_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:21:39.550335+00:00
-- url     : https://prove2.me/submissions/bfe4c62a-5456-42e7-89e7-43bce0f2d7d0

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

namespace AvramChat06

/-- The exact exponential survival kernel factors *inside* the
age-distribution lintegral, for arbitrary nonnegative measurable
age laws. The result needs no finite support, discretisation,
or continuity-of-probability limiting argument. -/
theorem exponential_tail_lintegral_random_age_scaling
    (μ ν : Measure ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hAge : ∀ᵐ a ∂μ, 0 ≤ a)
    (hTail : ∀ u : ℝ, 0 ≤ u →
       ν (Ioi u) = ENNReal.ofReal (Real.exp (-u))) :
    (∫⁻ a, ν (Ioi (a + t)) ∂μ) =
      (∫⁻ a, ν (Ioi a) ∂μ) *
        ENNReal.ofReal (Real.exp (-t)) := by
  have hAE : (fun a => ν (Ioi (a + t))) =ᵐ[μ]
      (fun a => ν (Ioi a) *
        ENNReal.ofReal (Real.exp (-t))) := by
    filter_upwards [hAge] with a ha
    rw [hTail (a + t) (add_nonneg ha ht),
      hTail a ha]
    rw [show -(a + t) = -a + -t by ring,
      Real.exp_add, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  calc
    (∫⁻ a, ν (Ioi (a + t)) ∂μ) =
        ∫⁻ a, ν (Ioi a) *
          ENNReal.ofReal (Real.exp (-t)) ∂μ :=
      lintegral_congr_ae hAE
    _ = (∫⁻ a, ν (Ioi a) ∂μ) *
          ENNReal.ofReal (Real.exp (-t)) := by
      rw [lintegral_mul_const' (ENNReal.ofReal (Real.exp (-t)))
        (fun a => ν (Ioi a)) (by simp)]

end AvramChat06

open AvramChat06

theorem solution
    (μ ν : Measure ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hAge : ∀ᵐ a ∂μ, 0 ≤ a)
    (hTail : ∀ u : ℝ, 0 ≤ u →
       ν (Ioi u) = ENNReal.ofReal (Real.exp (-u))) :
    (∫⁻ a, ν (Ioi (a + t)) ∂μ) =
      (∫⁻ a, ν (Ioi a) ∂μ) *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact exponential_tail_lintegral_random_age_scaling
    μ ν t ht hAge hTail
