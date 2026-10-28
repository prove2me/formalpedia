-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_killed_scale_exp_clock_finite_unbounded_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:31:50.988871+00:00
-- url     : https://prove2.me/submissions/71df3eae-446f-415c-b648-feae2b24bad0

import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- The *actual* lower-history-killed q-scale reward has finite
independent exponential-clock expectation; no spatial kernel or
Wiener-Hopf independence is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (p : ℝ) (hp : 0 < p)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           0 ≤ x + X.X s z.1
      then ENNReal.ofReal
        (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞)
      ∂(P.prod (ProbabilityTheory.expMeasure (q + p)))) < ⊤ := by
  have hr : 0 < q + p := add_pos hq hp
  have hmid : 0 < q + p / 2 := by linarith
  obtain ⟨θ, hθ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation
      X hnbv (q + p / 2) hmid
  have hψ : q < X.ψ θ := by rw [hroot]; linarith
  have hgap : X.ψ θ < q + p := by rw [hroot]; linarith
  have hMomentRate :=
    chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
      P X (q + p) hr θ (le_of_lt hθ) hgap x
  have hProductNeTop :
      ENNReal.ofReal ((q + p) - X.ψ θ) *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp
            (θ * (x + X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (ProbabilityTheory.expMeasure (q + p)))) ≠ ⊤ := by
    rw [hMomentRate, ← ENNReal.ofReal_mul (le_of_lt hr)]
    simp
  have hRateNeZero : ENNReal.ofReal ((q + p) - X.ψ θ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hgap))
  have hMomentFinite :
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X (Real.toNNReal z.2) z.1)))
        ∂(P.prod (ProbabilityTheory.expMeasure (q + p)))) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right hProductNeTop hRateNeZero
  have hDom :=
    chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a
      P X (q + p) hr q W hW θ (le_of_lt hθ) hψ x
  exact lt_of_le_of_lt hDom
    (ENNReal.mul_lt_top (by exact ENNReal.ofReal_lt_top) hMomentFinite)
