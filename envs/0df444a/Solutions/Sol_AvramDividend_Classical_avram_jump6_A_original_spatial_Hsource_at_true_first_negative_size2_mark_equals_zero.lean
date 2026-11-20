-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:45:03.252648+00:00
-- url     : https://prove2.me/submissions/c3762f2a-6feb-4f49-8f23-d0c6ec1dbccf

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_finitecap_marked_ruin_discounted_original_reward_zero_no_future_exit
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
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (q : ℝ) (w : ℝ → ℝ)
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (H : ℕ → Ω → ℝ) (κ : ℕ → Ω → ℝ≥0)
    (k : ℕ) (hκ : κ k ω = σ)
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
    H k ω = 0 := by
  obtain ⟨hRuin, hCash⟩ :=
    avram_jump6_A_actual_finitecap_marked_ruin_discounted_original_reward_zero_no_future_exit
      X ω B N σ hPath hTube hBefore hMark w hwneg q
  have hNot : ¬ (σ = 0 ∨
      (σ : ℝ≥0∞) <
        ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) := by
    rw [hRuin]
    exact not_or_intro (ne_of_gt hσ) (lt_irrefl _)
  have hH := hHsource k ω
  rw [hκ] at hH
  simp only [hNot, ite_false] at hH
  exact hH.trans hCash
