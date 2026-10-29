-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:30:46.463259+00:00
-- url     : https://prove2.me/submissions/d97ffcb8-97ab-4c03-b742-cb0e5de571a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The original Lévy terminal exponential transform at its independent
exponential clock factorises into genuine supremum and drawdown transforms.
The ENNReal identity remains valid even when a moment is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (β : ℝ) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    (∫⁻ z, ENNReal.ofReal
       (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
       ∂(P.prod (expMeasure p))) =
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z))
          ∂(P.prod (expMeasure p))) *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure p))) := by
  classical
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z =>
    S z - X.X (Real.toNNReal z.2) z.1
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (β * s))
  let g : ℝ → ℝ≥0∞ := fun d => ENNReal.ofReal (Real.exp (-β * d))
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hS : Measurable S := by
    simpa only [S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D := by
    simpa only [D, S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hInd : IndepFun S D (P.prod (expMeasure p)) :=
    avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun X p hp
  have hFact :
      (∫⁻ z, f (S z) * g (D z) ∂(P.prod (expMeasure p))) =
      (∫⁻ z, f (S z) ∂(P.prod (expMeasure p))) *
      (∫⁻ z, g (D z) ∂(P.prod (expMeasure p))) := by
    have hTest : IndepFun (f ∘ S) (g ∘ D)
        (P.prod (expMeasure p)) := hInd.comp hf hg
    change (∫⁻ z, (f ∘ S) z * (g ∘ D) z
        ∂(P.prod (expMeasure p))) =
      (∫⁻ z, (f ∘ S) z ∂(P.prod (expMeasure p))) *
      (∫⁻ z, (g ∘ D) z ∂(P.prod (expMeasure p)))
    exact ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (hf.comp hS) (hg.comp hD) hTest
  have hPath (z : Ω × ℝ) :
      ENNReal.ofReal (Real.exp (β * X.X (Real.toNNReal z.2) z.1)) =
        f (S z) * g (D z) := by
    have hReal : β * X.X (Real.toNNReal z.2) z.1 =
        β * S z + -β * D z := by
      dsimp [D]
      ring
    rw [hReal, Real.exp_add]
    change ENNReal.ofReal
      (Real.exp (β * S z) * Real.exp (-β * D z)) =
        ENNReal.ofReal (Real.exp (β * S z)) *
        ENNReal.ofReal (Real.exp (-β * D z))
    exact ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))
  calc
    (∫⁻ z, ENNReal.ofReal
        (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
        ∂(P.prod (expMeasure p))) =
      ∫⁻ z, f (S z) * g (D z) ∂(P.prod (expMeasure p)) := by
        exact lintegral_congr hPath
    _ = _ := hFact
