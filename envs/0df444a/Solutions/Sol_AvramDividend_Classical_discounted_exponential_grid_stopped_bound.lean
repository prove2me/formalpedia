-- Prove2me | solution 1 for AvramDividend.Classical.discounted_exponential_grid_stopped_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:12:37.10291+00:00
-- url     : https://prove2.me/submissions/d40b9165-ebf2-468a-9ff6-ef842e487d72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_discounted_exponential_levy_supermartingale
import Theorems.Thm_AvramDividend_Classical_supermartingale_sample_nat
import Theorems.Thm_AvramDividend_Classical_sampled_hittingBtwn_supermartingale_expected_le
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (U : ℕ → Ω → ℝ) (hU : Adapted 𝓖 U) (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * X.X (n : ℝ≥0) ω - ((n : ℝ≥0) : ℝ) * q))
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let V : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * X.X (n : ℝ≥0) ω - ((n : ℝ≥0) : ℝ) * q)
  have hS : Supermartingale V 𝓖 P := by
    exact supermartingale_sample_nat h𝓖
      (fun t ω => Real.exp (θ * X.X t ω - (t : ℝ) * q))
      (discounted_exponential_levy_supermartingale X θ q hθ hψ)
  have hBound :=
    sampled_hittingBtwn_supermartingale_expected_le U V hU hS N
  have hZero : (∫ ω, V 0 ω ∂P) = 1 := by
    simpa only [V, Nat.cast_zero, NNReal.coe_zero, zero_mul, mul_zero, sub_zero] using
      (levy_compensated_exponential_expectation_one X 0 θ hθ)
  change (∫ ω, stoppedValue V
    (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤ 1
  exact hBound.trans_eq hZero
