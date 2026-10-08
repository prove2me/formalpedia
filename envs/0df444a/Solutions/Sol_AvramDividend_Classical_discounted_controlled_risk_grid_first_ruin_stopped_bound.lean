-- Prove2me | solution 1 for AvramDividend.Classical.discounted_controlled_risk_grid_first_ruin_stopped_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:23:47.302749+00:00
-- url     : https://prove2.me/submissions/6ffe465d-e5b1-43dd-9f58-6944189d132a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_exponential_supermartingale
import Theorems.Thm_AvramDividend_Classical_supermartingale_sample_nat
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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
          ((n : ℝ≥0) : ℝ) * q))
      (fun ω => ((hittingBtwn
        (fun n : ℕ => fun ω => riskProcess X x D (n : ℝ≥0) ω)
        (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      ∫ ω, Real.exp (θ * riskProcess X x D 0 ω) ∂P := by
  let U : ℕ → Ω → ℝ := fun n ω =>
    riskProcess X x D (n : ℝ≥0) ω
  let V : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
      ((n : ℝ≥0) : ℝ) * q)
  letI : IsProbabilityMeasure P := X.isProbability
  have hU : Adapted 𝓖 U := by
    intro n
    change Measurable[𝓖 n] (riskProcess X x D (n : ℝ≥0))
    rw [h𝓖 n]
    exact riskProcess_adapted X x D hD (n : ℝ≥0)
  have hV : Supermartingale V 𝓖 P :=
    supermartingale_sample_nat h𝓖
      (fun t ω => Real.exp (θ * riskProcess X x D t ω - (t : ℝ) * q))
      (discounted_controlled_risk_exponential_supermartingale
        X x D hD θ q hθ hψ)
  have hBound :=
    sampled_hittingBtwn_supermartingale_expected_le U V hU hV N
  change (∫ ω, stoppedValue V
    (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
    ∫ ω, Real.exp (θ * riskProcess X x D 0 ω) ∂P
  calc
    (∫ ω, stoppedValue V
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
        ∫ ω, V 0 ω ∂P := hBound
    _ = ∫ ω, Real.exp (θ * riskProcess X x D 0 ω) ∂P := by
      simp only [V, Nat.cast_zero, NNReal.coe_zero, zero_mul, sub_zero]
