-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:23:00.445906+00:00
-- url     : https://prove2.me/submissions/2f4fa6b2-5af7-4f22-9931-5dea72e87fe9

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Actual complete discounted Stieltjes dividend correction as a signed real inequality, including the zero atom and both cap contacts. -/
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
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω)) ≤ 0 := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω T hPre
  have hCover : rightLimit D T ω ≤ x + X.X T ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hStrategy.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hStrategy.1 ω] using hm
  have hRightNonneg : 0 ≤ rightLimit D T ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hStrategy ω T)
  have hOrder : x + X.X T ω - rightLimit D T ω ≤ x + X.X T ω := by
    linarith only [hRightNonneg]
  have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    (x + X.X T ω - rightLimit D T ω) (x + X.X T ω)
    (sub_nonneg.mpr hCover) hOrder
  have hDropNonneg : 0 ≤
      V (x + X.X T ω) -
        V (x + X.X T ω - rightLimit D T ω) := by
    linarith only [hSec, hRightNonneg]
  have hBudget := avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω T hPre
  have hReal := ENNReal.toReal_mono (by simp) hBudget
  rw [ENNReal.toReal_ofReal hDropNonneg] at hReal
  linarith only [hReal]
