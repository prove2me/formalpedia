-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_uniform_point_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:38:24.287172+00:00
-- url     : https://prove2.me/submissions/c44b8942-48d6-439f-95ff-e33f9ebd0aa1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual finite-cap dividend secant has bounded discounted norm
at every stopped payment time, including all boundary and atom contacts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s : ℝ)
    (hs : s ∈ paymentTimes (ruinTime X x D ω)) :
    ‖Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))‖ ≤
      (w C.toReal - C.toReal) - w 0 := by
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
  have hSec := avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
    C hC hCfinite w V hw_cont hw_smooth hw_grad hVfinite
    y δ hy hδ
  let R : ℝ := δ + V y - V (y + δ)
  let L : ℝ := (w C.toReal - C.toReal) - w 0
  have hRhi : R ≤ 0 := by
    dsimp [R]
    linarith only [hSec.1]
  have hRlo : -L ≤ R := by
    dsimp [R, L]
    linarith only [hSec.2]
  have hExpLe : Real.exp (-(q * s)) ≤ 1 := by
    have hn : -(q * s) ≤ (0 : ℝ) :=
      neg_nonpos.mpr (mul_nonneg hq hsPay.1)
    simpa using (Real.exp_le_exp.mpr hn)
  have hAbs : |Real.exp (-(q * s)) * R| =
      Real.exp (-(q * s)) * (-R) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonpos hRhi]
  change |Real.exp (-(q * s)) * R| ≤ L
  rw [hAbs]
  calc
    Real.exp (-(q * s)) * (-R) ≤ 1 * (-R) :=
      mul_le_mul_of_nonneg_right hExpLe (neg_nonneg.mpr hRhi)
    _ = -R := by ring
    _ ≤ L := by linarith only [hRlo]
