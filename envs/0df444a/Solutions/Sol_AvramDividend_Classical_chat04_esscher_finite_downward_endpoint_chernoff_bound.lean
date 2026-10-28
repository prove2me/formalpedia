-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_finite_downward_endpoint_chernoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T22:55:01.006641+00:00
-- url     : https://prove2.me/submissions/796ebed7-fe54-499f-9a0f-efaa0b08e51d

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_endpoint_markov_bound
import Theorems.Thm_AvramDividend_Classical_ennreal_exp_downcrossing_threshold_iff
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε b : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 < ε) (hεθ : ε ≤ θ) :
    ENNReal.ofReal (Real.exp (ε * b)) *
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))
        {ω : Ω | X.X t ω ≤ -b} ≤
      ENNReal.ofReal
        (Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by
  have hevent :
      {ω : Ω | ENNReal.ofReal (Real.exp (ε * b)) ≤
          ENNReal.ofReal (Real.exp (-ε * X.X t ω))} =
      {ω : Ω | X.X t ω ≤ -b} := by
    ext ω
    exact ennreal_exp_downcrossing_threshold_iff
      ε b (X.X t ω) hε
  simpa only [hevent] using
    chat04_esscher_finite_negative_endpoint_markov_bound
      X t θ ε b hθ (le_of_lt hε) hεθ
