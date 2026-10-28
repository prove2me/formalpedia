-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_clock_survival_cdf_to_real_iInf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:58:55.125421+00:00
-- url     : https://prove2.me/submissions/4fab5f18-8c34-4a8a-bacc-74e827850f51

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_esscher_true_exp_rate_cdf_abel_limit
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The true exponential-clock-weighted Esscher survival CDF converges
    to the real perpetual survival infimum without any WH hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto
      (fun n : ℕ => ∫ v : ℝ,
        (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ Real.toNNReal v →
            0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X (Real.toNNReal v) ω -
              (Real.toNNReal v : ℝ) *
                laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
        ∂ProbabilityTheory.expMeasure (p n))
      atTop
      (nhds (⨅ t : ℝ≥0, ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by
  let F : ℝ≥0 → ℝ := fun t =>
    ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P
  have hanti : Antitone F := by
    intro t u htu
    exact esscher_weighted_lower_survival_mass_antitone X θ hθ x t u htu
  have hmeas : Measurable (fun v : ℝ => F (Real.toNNReal v)) :=
    hanti.measurable.comp measurable_real_toNNReal
  have hbound (v : ℝ) : ‖F (Real.toNNReal v)‖ ≤ (1 : ℝ) := by
    obtain ⟨h0, h1⟩ :=
      esscher_weighted_lower_survival_mass_unit_interval
        X θ hθ x (Real.toNNReal v)
    change 0 ≤ F (Real.toNNReal v) at h0
    change F (Real.toNNReal v) ≤ 1 at h1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hlim : Tendsto (fun v : ℝ => F (Real.toNNReal v))
      atTop (nhds (⨅ t : ℝ≥0, F t)) :=
    (esscher_weighted_lower_survival_mass_tendsto_iInf
      X θ hθ x).comp Real.tendsto_toNNReal_atTop
  have h := esscher_true_exp_rate_cdf_abel_limit
    (fun v : ℝ => F (Real.toNNReal v))
    (⨅ t : ℝ≥0, F t) hlim hmeas hbound p hp hpos
  simpa only [F] using h
