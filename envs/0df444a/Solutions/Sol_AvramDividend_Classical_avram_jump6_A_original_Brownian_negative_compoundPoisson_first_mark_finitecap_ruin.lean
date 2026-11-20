-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_Brownian_negative_compoundPoisson_first_mark_finitecap_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:46:37.306492+00:00
-- url     : https://prove2.me/submissions/311060fe-3ac7-4a6f-bac7-fcf223b29263

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B J : ℝ≥0 → ℝ) (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t + J t)
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hJneg : ∀ t : ℝ≥0, t ≤ σ → J t ≤ 0)
    (hMark : J σ ≤ -2) :
    (∀ t : ℝ≥0, t ≤ σ →
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω = 0) ∧
    riskProcess X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω < 0 := by
  have hPay (t : ℝ≥0) (ht : t ≤ σ) :
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω = 0 := by
    apply barrierStrategy_zero_before_upcrossing
    intro s hs
    rw [hPath s]
    have hb : B s < (1 / 4000 : ℝ) :=
      (abs_lt.mp (hTube s (le_trans hs ht))).2
    have hj := hJneg s (le_trans hs ht)
    nlinarith
  constructor
  · exact hPay
  · change (1 / 10 : ℝ) + X.X σ ω -
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω < 0
    rw [hPay σ le_rfl, hPath σ]
    have hb : B σ < (1 / 4000 : ℝ) :=
      (abs_lt.mp (hTube σ le_rfl)).2
    nlinarith
