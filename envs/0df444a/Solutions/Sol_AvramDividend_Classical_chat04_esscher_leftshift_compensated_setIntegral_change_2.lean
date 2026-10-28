-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_leftshift_compensated_setIntegral_change
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:31:30.380793+00:00
-- url     : https://prove2.me/submissions/6036b017-80d5-483c-8f87-d98abcd68f33

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A,
      Real.exp (-ε * X.X t ω -
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
    (∫ ω in A,
      Real.exp ((θ - ε) * X.X t ω -
        (t : ℝ) * X.ψ (θ - ε)) ∂P) := by
  have hm : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hf : Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))) := by fun_prop
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hA]
  congr 1
  funext ω
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add]
  congr 1
  ring
