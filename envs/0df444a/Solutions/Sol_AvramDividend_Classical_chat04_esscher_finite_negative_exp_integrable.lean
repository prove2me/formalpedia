-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_finite_negative_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:45:38.931507+00:00
-- url     : https://prove2.me/submissions/3a9c7360-5bf7-45ce-8130-98e07caef2a5

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ) (hθ : 0 ≤ θ)
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    Integrable (fun ω => Real.exp (-ε * X.X t ω))
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) := by
  have hmX : Measurable (X.X t) := X.adapted.measurable
  have hmReal : Measurable (fun ω : Ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hmX).sub measurable_const)
  have hmF : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))) :=
    ENNReal.measurable_ofReal.comp hmReal
  have hfin : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) < ∞ :=
    Filter.Eventually.of_forall (fun ω => ENNReal.ofReal_lt_top)
  rw [integrable_withDensity_iff hmF hfin]
  have heq :
      (fun ω : Ω =>
        Real.exp (-ε * X.X t ω) *
          (ENNReal.ofReal
            (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))).toReal) =
      (fun ω : Ω =>
        Real.exp (-(t : ℝ) * X.ψ θ) *
          Real.exp ((θ - ε) * X.X t ω)) := by
    funext ω
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact ((X.laplace t (θ - ε) (sub_nonneg.mpr hεθ)).1).const_mul _
