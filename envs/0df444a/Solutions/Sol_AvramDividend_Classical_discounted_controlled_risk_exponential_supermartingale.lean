-- Prove2me | solution 1 for AvramDividend.Classical.discounted_controlled_risk_exponential_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:35:25.891127+00:00
-- url     : https://prove2.me/submissions/2c3d6a65-6a64-468f-b6f2-b1b2fb679318

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_controlled_levy_exponential_supermartingale

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * riskProcess X x D t ω - (t : ℝ) * q)) 𝓕 P := by
  have hS :=
    discounted_controlled_levy_exponential_supermartingale
      X D hD θ q hθ hψ
  have hPos : 0 ≤ Real.exp (θ * x) := (Real.exp_pos _).le
  have hScaled := hS.smul_nonneg hPos
  have hEq :
      (Real.exp (θ * x)) •
        (fun t ω => Real.exp (θ * (X.X t ω - D t ω) - (t : ℝ) * q)) =
      (fun t ω =>
        Real.exp (θ * riskProcess X x D t ω - (t : ℝ) * q)) := by
    funext t ω
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold riskProcess
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hEq] at hScaled
  exact hScaled
