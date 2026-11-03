-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:40:37.065976+00:00
-- url     : https://prove2.me/submissions/28a802d4-ee5d-4035-90f6-f023355b1a66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_discounted_right_endpoint_cell_upper_error

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Right-endpoint source-frozen value drop plus exact full-Stieltjes mesh error.
    No finite-variation assumption is imposed on the source Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal
          (V (x + X.X b ω - rightLimit D a ω) -
            V (x + X.X b ω - rightLimit D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω b hPre
  have hCover : rightLimit D b ω ≤ x + X.X b ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hmono : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone D hStrategy ω) hab
  have hpost : 0 ≤ x + X.X b ω - rightLimit D b ω := sub_nonneg.mpr hCover
  have horder :
      x + X.X b ω - rightLimit D b ω ≤
        x + X.X b ω - rightLimit D a ω := by
    linarith only [hmono]
  have hsec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    (x + X.X b ω - rightLimit D b ω)
    (x + X.X b ω - rightLimit D a ω) hpost horder
  have hdrop : rightLimit D b ω - rightLimit D a ω ≤
      V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω) := by
    linarith only [hsec]
  have hmass :
      dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
        ENNReal.ofReal
          (V (x + X.X b ω - rightLimit D a ω) -
            V (x + X.X b ω - rightLimit D b ω)) := by
    rw [dividendMeasure_Ioc_rightLimit D hStrategy ω a b]
    exact ENNReal.ofReal_le_ofReal hdrop
  have hexp : 0 ≤ Real.exp (-(q * (b : ℝ))) := le_of_lt (Real.exp_pos _)
  have hwidth : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr (by exact_mod_cast hab)
  have herr : 0 ≤ q * ((b : ℝ) - (a : ℝ)) := mul_nonneg hq hwidth
  calc
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
          (Real.exp (-(q * (b : ℝ))) + q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) :=
      avram_wave6_08_discounted_right_endpoint_cell_upper_error
        q hq (dividendMeasure D ω) (a : ℝ) (b : ℝ)
        (by exact_mod_cast (show (0 : ℝ≥0) ≤ a from bot_le)) (by exact_mod_cast hab)
    _ =
      (ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) +
        ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
      rw [ENNReal.ofReal_add hexp herr]
    _ =
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
      rw [add_mul]
    _ ≤ _ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmass bot_le)
        (le_refl _)
