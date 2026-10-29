-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_actual_Qp_all_borel_nonnegative_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:11:09.675972+00:00
-- url     : https://prove2.me/submissions/6772ca7a-43b5-4ded-abaa-ab08d47dc0de

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- All nonnegative measurable tests of the genuine Esscher-clock
supremum and drawdown have a factorised joint expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    let Qp : Measure (Ω × ℝ) :=
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    (∫⁻ z, f (S z) * g (D z) ∂Qp) =
      (∫⁻ z, f (S z) ∂Qp) * (∫⁻ z, g (D z) ∂Qp) := by
  classical
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
    (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z =>
    S z - X.X (Real.toNNReal z.2) z.1
  have hS : Measurable S := by
    simpa only [S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D := by
    simpa only [D, S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hInd : IndepFun S D Qp :=
    avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
      X θ p hθ hp hJoint
  have hTest : IndepFun (f ∘ S) (g ∘ D) Qp := hInd.comp hf hg
  change (∫⁻ z, (f ∘ S) z * (g ∘ D) z ∂Qp) =
    (∫⁻ z, (f ∘ S) z ∂Qp) * (∫⁻ z, (g ∘ D) z ∂Qp)
  exact ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hf.comp hS) (hg.comp hD) hTest
