-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:37:34.867132+00:00
-- url     : https://prove2.me/submissions/813abdb2-cfec-4d35-be73-76d8dcfce282

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_nat_positive_martingale_finite_grid_maximal_unit_bound
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
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ i : ℕ, g i ≤ T)
    (a : ℝ≥0) (n : ℕ) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
        {ω : Ω | (a : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => Real.exp
              (-ε * X.X (g k) ω -
                (g k : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))} ≤ 1 := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω =>
    ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let Z : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (-ε * X.X (g k) ω -
      (g k : ℝ) * (X.ψ (θ - ε) - X.ψ θ))
  haveI hprob : IsProbabilityMeasure Q := by
    dsimp [Q]
    simpa only [SpectrallyNegativeLevy.ψ] using
      chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  obtain ⟨𝓖, h𝓖, hmart⟩ :=
    chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
      X θ ε hθ hε hεθ T g hg hgT
  have hpos : ∀ k ω, 0 ≤ Z k ω := by
    intro k ω
    exact Real.exp_nonneg _
  have hunit : ∀ k, (∫ ω, Z k ω ∂Q) = 1 := by
    intro k
    simpa only [Z, Q] using
      chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
        X θ ε hθ hε hεθ (g k) T (hgT k)
  have hbound :=
    nat_positive_martingale_finite_grid_maximal_unit_bound
      Z hmart hpos hunit a n
  simpa only [Z, Q] using hbound
