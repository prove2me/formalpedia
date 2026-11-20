-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_positive_psi_root_true_fixedhorizon_expsup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:30:45.454115+00:00
-- url     : https://prove2.me/submissions/f61e8ae9-d910-4e1b-b371-715cac2c0435

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a39_original_exponential_clock_supremum_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_positive
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : 0 ≤ β) (hβlam : β < lam)
    (n : ℝ≥0) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (β * runningSup X n ω))
      ∂ P) < ⊤ := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  have hTail : 0 < expMeasure p (Ioi (n : ℝ)) :=
    avram_ws01e_b_expMeasure_strict_survival_positive
      p (n : ℝ) hp n.property
  have hMoment :=
    avram_ga_a39_original_exponential_clock_supremum_integrable
      X p lam β hp hlam hroot hβlam
  exact avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
    X (expMeasure p) n β hβ hTail hMoment
