-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:47:38.422092+00:00
-- url     : https://prove2.me/submissions/fe635c83-da90-4824-912d-68e615c8f31a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_interval_full_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine signed correction for the complete discounted Stieltjes measure on a capped time cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (y : ℝ)
    (hy : rightLimit D b ω ≤ y) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (y - rightLimit D b ω) - V (y - rightLimit D a ω) ≤ 0 := by
  have hMono : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD ω) hab
  have hPost : 0 ≤ y - rightLimit D b ω := sub_nonneg.mpr hy
  have hOrder : y - rightLimit D b ω ≤ y - rightLimit D a ω := by
    linarith only [hMono]
  have hSec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (y - rightLimit D b ω) (y - rightLimit D a ω)
    hPost hOrder
  rw [←hV (y - rightLimit D a ω),
      ←hV (y - rightLimit D b ω)] at hSec
  have hDrop : 0 ≤ V (y - rightLimit D a ω) -
      V (y - rightLimit D b ω) := by
    linarith only [hSec, hMono]
  have hBound := avram_wave5_04b_caplinear_interval_full_stieltjes_budget
    c hc q hq w hw_cont hw_smooth hw_grad D hD ω a b hab y hy
  rw [←hV (y - rightLimit D a ω),
      ←hV (y - rightLimit D b ω)] at hBound
  have hReal := ENNReal.toReal_mono (by simp) hBound
  rw [ENNReal.toReal_ofReal hDrop] at hReal
  linarith only [hReal]
