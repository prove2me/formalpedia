-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_allcap_actual_real_clock_forward_secant_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:04:53.000553+00:00
-- url     : https://prove2.me/submissions/b91a2446-c503-48b0-8ca4-efde5df66224

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- At every genuine ruin-stopped payment time, including reserve zero,
cap contact and the time-zero atom, the actual post-payment forward secant
is nonpositive for finite OR infinite positive caps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 ≤ δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s : ℝ)
    (hs : s ∈ paymentTimes (ruinTime X x D ω)) :
    Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))
      ≤ 0 := by
  have hsPay := hs
  change s ∈ Ici (0 : ℝ) ∩
    ({0} ∪ {t : ℝ | ENNReal.ofReal t < ruinTime X x D ω}) at hsPay
  have hPreS : s.toNNReal = 0 ∨
      (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
    rcases hsPay.2 with hzero | hlt
    · left
      have heq : s = 0 := by simpa using hzero
      simp only [heq, Real.toNNReal_zero]
    · right
      change (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hlt
      exact hlt
  have hCover := hD.1.2 ω s.toNNReal hPreS
  dsimp [riskProcess] at hCover
  let y : ℝ := x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω
  have hy : 0 ≤ y := by linarith only [hCover]
  have horder : y ≤ y + δ := le_add_of_nonneg_right hδ
  have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    y (y + δ) hy horder
  have hR : δ + V y - V (y + δ) ≤ 0 := by
    dsimp [y] at hSec ⊢
    linarith only [hSec]
  change Real.exp (-(q * s)) *
    (δ + V y - V (y + δ)) ≤ 0
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hR
