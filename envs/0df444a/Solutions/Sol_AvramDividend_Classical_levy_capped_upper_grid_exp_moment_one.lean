-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upper_grid_exp_moment_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:08:59.360101+00:00
-- url     : https://prove2.me/submissions/2b94dc87-a201-41cc-9ddd-9e34384a30db

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ) :
    (∫ ω,
      let K := hittingBtwn (fun k ω => X.X (clock k) ω)
        (Ioi z) 0 m ω
      Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ) ∂P) = 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  let M : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (θ * X.X (clock k) ω - (clock k : ℝ) * X.ψ θ)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hM : Martingale M H P := by
    exact chat03_martingale_sampled_filtration_reindex_corrected
      (fun t ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))
      (levy_compensated_exponential_martingale X θ hθ)
      clock hc H hH
  have hstop := chat03_bounded_first_crossing_martingale_identity
    Z M hZ hM z m
  have hzero : ∀ ω : Ω, M 0 ω = 1 := by
    intro ω
    simp [M, hc0, X.X_zero ω]
  have hint : (∫ ω, M 0 ω ∂P) = 1 := by
    simp_rw [hzero]
    simp
  change (∫ ω, M (hittingBtwn Z (Ioi z) 0 m ω) ω ∂P) = 1
  exact hstop.trans hint
