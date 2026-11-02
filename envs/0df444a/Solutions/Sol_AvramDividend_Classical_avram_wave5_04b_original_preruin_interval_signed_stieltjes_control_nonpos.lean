-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:59:47.930306+00:00
-- url     : https://prove2.me/submissions/80258f32-de30-4600-941b-d3e0020670d8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original Levy-source signed full-Stieltjes correction on each pre-ruin dividend interval. -/
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
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω b hPre
  have hCover : rightLimit D b ω ≤ x + X.X b ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  exact avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos
    c hc q hq w V hw_cont hw_smooth hw_grad hV
    D hStrategy ω a b hab (x + X.X b ω) hCover
