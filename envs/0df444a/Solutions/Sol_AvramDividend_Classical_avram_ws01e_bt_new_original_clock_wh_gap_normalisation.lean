-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_wh_gap_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:36:45.651978+00:00
-- url     : https://prove2.me/submissions/d29362e8-aea6-4a01-b42c-b06007596f57

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The two genuine original-clock Wiener–Hopf factors have the
exact finite-rate normalisation at every positive moment gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (β : ℝ)
    (hβ : 0 ≤ β) (hgap : X.ψ β < p) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    ENNReal.ofReal (p - X.ψ β) *
      ((∫⁻ z, ENNReal.ofReal (Real.exp (β * S z))
          ∂(P.prod (expMeasure p))) *
       (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure p)))) =
      ENNReal.ofReal p := by
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z =>
    S z - X.X (Real.toNNReal z.2) z.1
  have hMoment :
      ENNReal.ofReal (p - X.ψ β) *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal
            (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
          ∂(P.prod (expMeasure p))) =
      ENNReal.ofReal p := by
    simpa using
      (chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
        P X p hp β hβ hgap 0)
  have hFactor :
      (∫⁻ z : Ω × ℝ,
         ENNReal.ofReal
           (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
         ∂(P.prod (expMeasure p))) =
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z))
          ∂(P.prod (expMeasure p))) *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure p))) :=
    avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor X p hp β
  rw [hFactor] at hMoment
  exact hMoment
