-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:56:02.171604+00:00
-- url     : https://prove2.me/submissions/9bc0befd-15fc-4da5-9ccc-bda5385c86b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual time-zero Stieltjes atom and cap-linear value change have nonpositive signed correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) :
    (∫⁻ s in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X 0 ω - rightLimit D 0 ω) -
      V (x + X.X 0 ω) ≤ 0 := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω (0 : ℝ≥0) (Or.inl rfl)
  have hCover : rightLimit D 0 ω ≤ x + X.X 0 ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hDnonneg : 0 ≤ D 0 ω := by
    have hm := hStrategy.2.1 ω
      (show (0 : ℝ≥0) ≤ (0 : ℝ≥0) from zero_le)
    simpa only [hStrategy.1 ω] using hm
  have hRightNonneg : 0 ≤ rightLimit D 0 ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hStrategy ω 0)
  have hOrder : x + X.X 0 ω - rightLimit D 0 ω ≤ x + X.X 0 ω := by
    linarith only [hRightNonneg]
  have hSec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (x + X.X 0 ω - rightLimit D 0 ω) (x + X.X 0 ω)
    (sub_nonneg.mpr hCover) hOrder
  rw [←hV (x + X.X 0 ω),
      ←hV (x + X.X 0 ω - rightLimit D 0 ω)] at hSec
  have hDrop : 0 ≤ V (x + X.X 0 ω) -
      V (x + X.X 0 ω - rightLimit D 0 ω) := by
    linarith only [hSec, hRightNonneg]
  have hBound := avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω
  rw [←hV (x + X.X 0 ω),
      ←hV (x + X.X 0 ω - rightLimit D 0 ω)] at hBound
  have hReal := ENNReal.toReal_mono (by simp) hBound
  rw [ENNReal.toReal_ofReal hDrop] at hReal
  linarith only [hReal]
