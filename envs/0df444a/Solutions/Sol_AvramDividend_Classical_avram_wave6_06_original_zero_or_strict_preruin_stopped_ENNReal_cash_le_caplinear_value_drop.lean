-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:51:18.872211+00:00
-- url     : https://prove2.me/submissions/33d39046-743e-45cf-ba6f-25e3e75ec4bf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The signed original full Stieltjes real cash is genuinely finite by
    admissibility, so its caplinear value-drop bound holds in ENNReal itself. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (V (x + X.X (τ ω) ω) -
         V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) := by
  let Cash : ℝ≥0∞ :=
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  have hCashBound :
      Cash ≤ ENNReal.ofReal (rightLimit D (τ ω) ω) := by
    dsimp [Cash]
    exact avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
      q hq D hD.1.1 ω (ruinTime X x D ω) (τ ω)
  have hCashFinite : Cash ≠ ⊤ := by
    have hlt : Cash < (⊤ : ℝ≥0∞) :=
      lt_of_le_of_lt hCashBound (by simp)
    exact ne_of_lt hlt
  have hSigned :=
    avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
      X x C q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω τ hPre
  have hReal :
      Cash.toReal ≤
        V (x + X.X (τ ω) ω) -
        V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) := by
    dsimp [Cash]
    linarith only [hSigned]
  change Cash ≤ ENNReal.ofReal
    (V (x + X.X (τ ω) ω) -
     V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
  calc
    Cash = ENNReal.ofReal Cash.toReal := (ENNReal.ofReal_toReal hCashFinite).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hReal
