-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_cash_le_exponential_controlLoss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:44:10.268983+00:00
-- url     : https://prove2.me/submissions/1468c6c8-f771-4e79-80a4-18a41c28cce7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact pathwise control loss bounds all original source-X weighted
Stieltjes cash increments, including their diffuse components. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (ω : Ω) :
    θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ≤
    ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let B : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  have hCell (i : ℕ) :
      θ * (Z (u (i + 1)) ω * B (u (i + 1)) ω *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ≤
      Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) := by
    have hm := avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD ω (hu (Nat.le_succ i))
    have hc := avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
      θ (rightLimit D (u i) ω) (rightLimit D (u (i + 1)) ω) hθ hm
    have hs := mul_le_mul_of_nonneg_left hc
      (Real.exp_pos (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ)).le
    dsimp [Z, B]
    nlinarith
  change θ * ∑ i ∈ Finset.range n,
    Z (u (i + 1)) ω * B (u (i + 1)) ω *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ≤
    ∑ i ∈ Finset.range n,
      Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact hCell i
