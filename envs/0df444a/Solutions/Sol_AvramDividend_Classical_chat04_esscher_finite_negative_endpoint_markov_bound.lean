-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_finite_negative_endpoint_markov_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:00:03.04542+00:00
-- url     : https://prove2.me/submissions/9e293db5-c29b-4b21-bed0-484ba8b8c88d

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_laplace_lintegral_exact
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε b : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    ENNReal.ofReal (Real.exp (ε * b)) *
      (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal
        (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))
        {ω : Ω | ENNReal.ofReal (Real.exp (ε * b)) ≤
          ENNReal.ofReal (Real.exp (-ε * X.X t ω))} ≤
      ENNReal.ofReal
        (Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by
  have hm : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hf : Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp (-ε * X.X t ω))) := by fun_prop
  rw [← chat04_esscher_finite_negative_laplace_lintegral_exact X t θ ε hθ hε hεθ]
  exact mul_meas_ge_le_lintegral hf _
