-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:34:52.434177+00:00
-- url     : https://prove2.me/submissions/e124ea1e-f4c1-4894-8ee1-5d03f6db260e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
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
    (hFirst : N σ = 1)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)))
    (hσsmall : (σ : ℝ) ≤ 1 / 10)
    (q : ℝ) (w : ℝ → ℝ)
    (hw : ∀ z : ℝ, w z =
      if z < 0 then 0 else 1 + z + z ^ 2)
    (H Jfull Drift : ℝ)
    (hH : H =
      Real.exp (-(q * (σ : ℝ))) *
        w (riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω) +
        (∫⁻ s in paymentTimes
            (ruinTime X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
            Iic (σ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal)
    (hJ : Jfull = -2 * (N σ : ℝ) + 2 * (σ : ℝ))
    (hDrift : Drift ≤ 0)
    (hLedger : H ≤ w (1 / 10 : ℝ) + B σ + Jfull + Drift) :
    False := by
  have hNeg : ∀ z : ℝ, z < 0 → w z = 0 := by
    intro z hz
    simp [hw z, hz]
  obtain ⟨_, hCashZero⟩ :=
    avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
      X ω B N σ u hPath hTube hBefore
      (by omega : 1 ≤ N σ) hu w hNeg q
  have hHz : H = 0 := by
    rw [hH]
    exact hCashZero
  have hJz : Jfull = -2 + 2 * (σ : ℝ) := by
    rw [hJ, hFirst]
    ring
  have hW : w (1 / 10 : ℝ) =
      1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2 := by
    rw [hw]
    norm_num
  have hb : B σ ≤ (1 / 100 : ℝ) := by
    have hb0 := (abs_lt.mp (hTube σ le_rfl)).2
    linarith
  have hGap :=
    (avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
      (1 / 10 : ℝ) (B σ) (σ : ℝ)
      (by norm_num) (by norm_num) hb hσsmall).2
  rw [hHz, hJz, hW] at hLedger
  linarith
