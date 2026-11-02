-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_cap_original_discounted_cell_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:55:45.154447+00:00
-- url     : https://prove2.me/submissions/9ec45b33-5097-497c-993e-723ad3f00bb3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A real signed dividend-control correction: full discounted dividendMeasure plus left-weighted source-frozen V change is nonpositive for every positive finite/infinite cap and all boundary reserve contacts. -/
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
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by
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
  have hDropNonneg : 0 ≤
      V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω) := by
    linarith only [hsec, hmono]
  have hWeighted :=
    avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
      X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω a b hab hPre
  have hExpNonneg : 0 ≤ Real.exp (-(q * (a : ℝ))) :=
    (Real.exp_pos _).le
  have hProductFinite :
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal (V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_mul hExpNonneg]
    simp
  have hReal := ENNReal.toReal_mono hProductFinite hWeighted
  rw [ENNReal.toReal_mul] at hReal
  rw [ENNReal.toReal_ofReal hExpNonneg,
      ENNReal.toReal_ofReal hDropNonneg] at hReal
  nlinarith only [hReal]
