-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_horizon_pre_rightpayment_secant_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:15:45.59699+00:00
-- url     : https://prove2.me/submissions/f0e9ba58-b65a-43d0-bf94-b9825fbfb2eb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (w : ℝ → ℝ)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∀ ω,
      0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)) ∧
    (∀ ω,
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          (rightLimit D S ω - D S ω) +
        Real.exp (-(q * T)) *
          w (riskProcess X x D S ω -
            (rightLimit D S ω - D S ω))
      else 0) ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)) := by
  let S : ℝ≥0 := ⟨T, hT⟩
  have hSpos : (0 : ℝ≥0) < S := by
    apply NNReal.coe_lt_coe.mp
    change (0 : ℝ) < T
    exact hTpos
  constructor
  · intro ω
    split_ifs with hs
    · exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (hw_nonneg ω S hSpos hs)
    · exact le_refl 0
  · intro ω
    split_ifs with hs
    · have hsec := hjump ω S (Or.inr hs)
      have hweight : 0 ≤ Real.exp (-(q * T)) :=
        le_of_lt (Real.exp_pos _)
      have hscaled := mul_le_mul_of_nonneg_left hsec hweight
      dsimp only [S] at hscaled
      nlinarith
    · exact le_refl 0
