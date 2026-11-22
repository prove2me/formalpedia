-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb49_predictable_real_condExp_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:35:26.202209+00:00
-- url     : https://prove2.me/submissions/8ac37317-2779-4a65-8464-074cf8d90000

import Mathlib
import Theorems.Thm_ShiOptRates_Stochastic_integral_inner_eq_zero_of_condExp_eq_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped InnerProductSpace
noncomputable section

/-- A predictable real coefficient is orthogonal in expectation to a
centred future martingale difference, provided their product is integrable. -/
theorem solution
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)]
    (A Q : Ω → ℝ)
    (hA : Measurable[m] A) (hQ : Integrable Q P)
    (hProd : Integrable (fun ω => A ω * Q ω) P)
    (hCond : P[Q | m] =ᵐ[P] (fun _ => (0 : ℝ))) :
    (∫ ω, A ω * Q ω ∂P) = 0 := by
  have hAe : AEStronglyMeasurable[m] A P :=
    hA.stronglyMeasurable.aestronglyMeasurable
  have hInnerI : Integrable (fun ω => ⟪A ω, Q ω⟫_ℝ) P := by
    simpa only [Real.inner_apply] using hProd
  have hZero :=
    ShiOptRates.Stochastic.integral_inner_eq_zero_of_condExp_eq_zero
      hm hAe hQ hInnerI hCond
  simpa only [Real.inner_apply] using hZero
