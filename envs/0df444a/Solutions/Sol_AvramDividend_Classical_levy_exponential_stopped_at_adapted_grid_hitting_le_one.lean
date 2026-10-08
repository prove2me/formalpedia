-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_stopped_at_adapted_grid_hitting_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:01:05.196976+00:00
-- url     : https://prove2.me/submissions/c5119ce5-60d4-4c05-bafb-ed73fcdd7f7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_martingale_sample_nat
import Theorems.Thm_AvramDividend_Classical_sampled_hittingBtwn_supermartingale_expected_le

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
    (θ : ℝ) (hθ : 0 ≤ θ)
    (U : ℕ → Ω → ℝ) (hU : Adapted 𝓖 U) (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * X.X (n : ℝ≥0) ω - ((n : ℝ≥0) : ℝ) * X.ψ θ))
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let V : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * X.X (n : ℝ≥0) ω - ((n : ℝ≥0) : ℝ) * X.ψ θ)
  have hM : Martingale V 𝓖 P := by
    exact martingale_sample_nat h𝓖
      (fun t ω => Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))
      (levy_compensated_exponential_martingale X θ hθ)
  have hS : Supermartingale V 𝓖 P := hM.supermartingale
  have hBound :=
    sampled_hittingBtwn_supermartingale_expected_le U V hU hS N
  have hZero : (∫ ω, V 0 ω ∂P) = 1 := by
    simpa only [V, Nat.cast_zero, NNReal.coe_zero] using
      (levy_compensated_exponential_expectation_one X 0 θ hθ)
  change (∫ ω, stoppedValue V
    (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤ 1
  exact hBound.trans_eq hZero
