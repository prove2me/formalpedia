-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:37:52.976058+00:00
-- url     : https://prove2.me/submissions/c0be8c03-c155-4251-a75f-4b793c1fcd76

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_nat_positive_martingale_finite_grid_maximal_unit_bound
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
  haveI : IsProbabilityMeasure (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  obtain ⟨𝓖, -, hM⟩ :=
    chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale X θ ε hθ hε hεθ T g hg hgT
  exact nat_positive_martingale_finite_grid_maximal_unit_bound _ hM
    (fun n ω => (Real.exp_pos _).le)
    (fun n => chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean X θ ε hθ hε hεθ _ T (hgT n))
    a n
