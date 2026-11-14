-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a60_original_BV_surviving_prepayment_dominates_afterpay_plus_right_dividend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:31:11.034416+00:00
-- url     : https://prove2.me/submissions/dc6a2774-823b-4f0e-b506-d892c36907bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q x : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ≥0) (ω : Ω)
    (hSurv : (T : ℝ≥0∞) < ruinTime X x D ω) :
    (x + X.X T ω - rightLimit D T ω =
      riskProcess X x D T ω -
        (rightLimit D T ω - D T ω)) ∧
    (Real.exp (-(q * (T : ℝ))) *
      (w (x + X.X T ω - rightLimit D T ω) +
        (rightLimit D T ω - D T ω)) ≤
      Real.exp (-(q * (T : ℝ))) *
        w (riskProcess X x D T ω)) := by
  have hPaid := hjump ω T (Or.inr hSurv)
  have hReserve :
      x + X.X T ω - rightLimit D T ω =
        riskProcess X x D T ω -
          (rightLimit D T ω - D T ω) := by
    simp only [riskProcess]
    ring
  constructor
  · exact hReserve
  · rw [hReserve]
    have hReward :
        w (riskProcess X x D T ω -
            (rightLimit D T ω - D T ω)) +
          (rightLimit D T ω - D T ω) ≤
            w (riskProcess X x D T ω) := by
      linarith [hPaid]
    exact mul_le_mul_of_nonneg_left hReward (le_of_lt (Real.exp_pos _))

