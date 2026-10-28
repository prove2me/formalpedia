-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_negative_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:32:51.742108+00:00
-- url     : https://prove2.me/submissions/2f20eb6e-bad0-46d8-a1b3-e361c983bc61

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    (∫ ω, Real.exp (-ε * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) := by
  have hm : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hf : Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hf
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun ω => (ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))).toReal •
      Real.exp (-ε * X.X t ω)) =
      fun ω => Real.exp (-((t : ℝ) * X.ψ θ)) * Real.exp ((θ - ε) * X.X t ω) := by
    funext ω
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [hfun, integral_const_mul, (X.laplace t (θ - ε) (by linarith)).2, ← Real.exp_add]
  congr 1
  simp only [SpectrallyNegativeLevy.ψ]
  ring
