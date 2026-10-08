-- Prove2me | solution 1 for AvramDividend.Classical.discounted_controlled_risk_bounded_grid_stopping_le_exp_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:36:56.84997+00:00
-- url     : https://prove2.me/submissions/6bd1a995-e567-4b2f-8b88-6a34f4f09ae9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_exponential_supermartingale
import Theorems.Thm_AvramDividend_Classical_supermartingale_sample_nat
import Theorems.Thm_AvramDividend_Classical_supermartingale_expected_stoppedValue_antitone_nat

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime 𝓖 τ)
    (N : ℕ) (hbdd : ∀ ω, τ ω ≤ (N : WithTop ℕ)) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
          ((n : ℝ≥0) : ℝ) * q))
      τ ω ∂P) ≤ Real.exp (θ * x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let V : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
      ((n : ℝ≥0) : ℝ) * q)
  have hV : Supermartingale V 𝓖 P :=
    supermartingale_sample_nat h𝓖
      (fun t ω => Real.exp (θ * riskProcess X x D t ω - (t : ℝ) * q))
      (discounted_controlled_risk_exponential_supermartingale
        X x D hD θ q hθ hψ)
  let τ0 : Ω → WithTop ℕ := fun _ => 0
  have hτ0 : IsStoppingTime 𝓖 τ0 := isStoppingTime_const 𝓖 0
  have hle : τ0 ≤ τ := by
    intro ω
    exact bot_le
  have hOptional :=
    supermartingale_expected_stoppedValue_antitone_nat
      hV hτ0 hτ hle hbdd
  have hStart (ω : Ω) : riskProcess X x D 0 ω = x := by
    unfold riskProcess
    rw [X.X_zero ω, hD.1 ω]
    ring
  have hMean : (∫ ω, V 0 ω ∂P) = Real.exp (θ * x) := by
    simp_rw [V, Nat.cast_zero, NNReal.coe_zero, zero_mul, sub_zero, hStart]
    simp
  change (∫ ω, stoppedValue V τ ω ∂P) ≤ Real.exp (θ * x)
  calc
    (∫ ω, stoppedValue V τ ω ∂P) ≤
        ∫ ω, stoppedValue V τ0 ω ∂P := hOptional
    _ = ∫ ω, V 0 ω ∂P := by simp [τ0, stoppedValue]
    _ = Real.exp (θ * x) := hMean
