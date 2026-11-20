-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:34:14.46361+00:00
-- url     : https://prove2.me/submissions/2e800a08-8ea2-4c11-b83c-f1b074eb6b26

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_physical_Brownian_size2_tube_forces_original_inclusive_barrier_cash_zero
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
    (σ u : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)))
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
        (σ : ℝ≥0∞) ∧
    Real.exp (-(q * (σ : ℝ))) *
      w (riskProcess X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
          Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal = 0 := by
  have hRuin :=
    avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
      X ω B N σ hPath hTube hBefore hMark
  have hNeg :=
    avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
      X ω B N σ hPath hTube hMark
  have hCash :=
    avram_jump6_A_physical_Brownian_size2_tube_forces_original_inclusive_barrier_cash_zero
      X ω B N σ u hPath hTube hu q
  constructor
  · exact hRuin
  · rw [hwneg _ hNeg, hCash]
    simp
