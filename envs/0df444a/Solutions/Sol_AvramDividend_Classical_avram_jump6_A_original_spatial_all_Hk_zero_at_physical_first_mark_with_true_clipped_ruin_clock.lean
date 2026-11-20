-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_all_Hk_zero_at_physical_first_mark_with_true_clipped_ruin_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:56:28.34445+00:00
-- url     : https://prove2.me/submissions/148646c6-027f-47ae-a6d9-4640386a28c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
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
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0) (hσ : 0 < σ)
    (hSmall : (σ : ℝ) ≤ 1 / 500)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (q : ℝ) (w : ℝ → ℝ)
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (H : ℕ → Ω → ℝ) (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hρ : ρ ω =
      (min (ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
        (1 : ℝ≥0∞)).toNNReal)
    (hκ : ∀ j, κ j ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((j : ℝ) + 1) ω)).toNNReal)
    (hHsource : ∀ j η, H j η =
      Real.exp (-(q * (κ j η : ℝ))) *
      w (if κ j η = 0 ∨
            (κ j η : ℝ≥0∞) <
              ruinTime X (1 / 10 : ℝ)
                (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) η then
          (1 / 10 : ℝ) + X.X (κ j η) η -
            rightLimit
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
              (κ j η) η
         else
           riskProcess X (1 / 10 : ℝ)
             (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
             (κ j η) η) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) η)
          ∩ Iic (κ j η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
           (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) η)).toReal) :
    ∀ k : ℕ, H k ω = 0 := by
  have hClock :=
    avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
      X ω B N σ ρ κ hPath hTube hBefore hMark hSmall hρ hκ
  intro k
  exact avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
    X ω B N σ hσ hPath hTube hBefore hMark
    q w hwneg H κ k (hClock k) hHsource
