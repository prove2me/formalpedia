-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_restricted_real_integral_factor_conditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:51:51.635993+00:00
-- url     : https://prove2.me/submissions/339a05f0-22b6-4f70-b07f-d6cef38e8f6b

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_restricted_lintegral_factor_conditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Nonnegative restricted ENNReal factorisation identifies real conditional means. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hApos : P A ≠ 0)
    (f : Ω → ℝ) (hNonneg : ∀ ω, 0 ≤ f ω)
    (hIntP : Integrable f P) (hIntCond : Integrable f (P[|A]))
    (hFactor :
      (∫⁻ ω in A, ENNReal.ofReal (f ω) ∂P) =
        P A * (∫⁻ ω, ENNReal.ofReal (f ω) ∂P)) :
    (∫ ω, f ω ∂(P[|A])) = ∫ ω, f ω ∂P := by
  have hL :=
    AvramDividend.Classical.avram_ws01e_bi_new_restricted_lintegral_factor_conditional
      P A hA hApos (fun ω => ENNReal.ofReal (f ω)) hFactor
  have heq : ENNReal.ofReal (∫ ω, f ω ∂(P[|A])) =
      ENNReal.ofReal (∫ ω, f ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hIntCond (ae_of_all _ hNonneg),
      ofReal_integral_eq_lintegral_ofReal hIntP (ae_of_all _ hNonneg)]
    exact hL
  have hC : 0 ≤ ∫ ω, f ω ∂(P[|A]) := integral_nonneg hNonneg
  have hP : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hNonneg
  have hre := congrArg ENNReal.toReal heq
  simpa only [ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hP] using hre
