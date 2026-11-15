-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24w_original_preleft_C2_arbitrary_increment_epsilon_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:56:00.18521+00:00
-- url     : https://prove2.me/submissions/02a32993-3cf5-4e7f-879b-359373dc21fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_hessian_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ω (t : ℝ≥0) (y : ℝ),
      let z := Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t
      z ∈ Icc a b → y ∈ Icc a b → z ≠ y →
      dist y z < δ →
      |w y - taylorWithinEval w 1 (uIcc z y) z y -
        (iteratedDeriv 2 w z * (y-z)^2) / 2| ≤
        ε * (y-z)^2  := by
  obtain ⟨δ, hδ, hMod⟩ :=
    avram_ubv_gauss13_localise_original_preleft_hessian_modulus
      X x D hD C w hw a b ha hab hbcap ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ω t y z hz hy hne hClose
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
      C w hw a b hBand _ _ hz hy hne
  have hξband : ξ ∈ Icc a b := by
    rcases le_total (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t) y with h | h
    · rw [Set.uIoo_of_le h] at hξ
      exact ⟨le_trans hz.1 hξ.1.le, le_trans hξ.2.le hy.2⟩
    · rw [Set.uIoo_of_ge h] at hξ
      exact ⟨le_trans hy.1 hξ.1.le, le_trans hξ.2.le hz.2⟩
  have hDist : dist ξ (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t) ≤
      dist y (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t) := by
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t) y with h | h
    · rw [Set.uIoo_of_le h] at hξ
      rw [abs_of_nonneg (sub_nonneg.mpr hξ.1.le),
          abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [hξ.2]
    · rw [Set.uIoo_of_ge h] at hξ
      rw [abs_of_nonpos (sub_nonpos.mpr hξ.2.le),
          abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hξ.1]
  have hModξ := hMod ω t ξ hz hξband (lt_of_le_of_lt hDist hClose)
  have hAbs : |iteratedDeriv 2 w ξ -
      iteratedDeriv 2 w (Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)| ≤ ε := by
    simpa only [Real.dist_eq] using le_of_lt hModξ
  rw [hTaylor]
  have hAlg :
      iteratedDeriv 2 w ξ *
          (y - Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) t)^2 / 2 -
        (iteratedDeriv 2 w (Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) t) *
          (y - Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) t)^2) / 2 =
        (iteratedDeriv 2 w ξ - iteratedDeriv 2 w
          (Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) t)) *
          (y - Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) t)^2 / 2 := by ring
  rw [hAlg]
  have hSq : 0 ≤ (y - Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)^2 := sq_nonneg _
  calc
    _ = |iteratedDeriv 2 w ξ - iteratedDeriv 2 w
        (Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) t)| *
        ((y - Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) t)^2 / 2) := by
          simp [abs_div, abs_mul, abs_of_nonneg hSq, mul_div_assoc]
    _ ≤ ε * ((y - Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) t)^2 / 2) :=
            mul_le_mul_of_nonneg_right hAbs (div_nonneg hSq (by norm_num))
    _ ≤ ε * (y - Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) t)^2 := by
            nlinarith [mul_nonneg (le_of_lt hε) hSq]
