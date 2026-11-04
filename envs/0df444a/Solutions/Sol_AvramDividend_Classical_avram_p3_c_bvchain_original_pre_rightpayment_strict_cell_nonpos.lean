-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:28.824443+00:00
-- url     : https://prove2.me/submissions/5d654f8a-0b36-4250-89ba-5dfa8ca4bcac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original strict-open Stieltjes control before the right dividend at b. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a < b)
    (hPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    (dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro s t hst
    exact (hStrategy.2.1 ω) (Real.toNNReal_mono hst)
  have hleft := dividendStrategy_real_extension_leftContinuous D hStrategy ω
  have horderR :
      Function.rightLim (fun s : ℝ => D s.toNNReal ω) (a : ℝ) ≤
        Function.leftLim (fun s : ℝ => D s.toNNReal ω) (b : ℝ) :=
    hmono.rightLim_le_leftLim (by exact_mod_cast hab)
  have hAB : rightLimit D a ω ≤ D b ω := by
    rw [dividendPath_real_rightLim_eq_rightLimit D ω
      (fun s t hst => hStrategy.2.1 ω hst) a] at horderR
    rw [(hleft (b : ℝ)).leftLim_eq] at horderR
    simpa only [Real.toNNReal_coe] using horderR
  have hSolv := hD.1.2 ω b (Or.inr hPre)
  have hCover : rightLimit D b ω ≤ x + X.X b ω := by
    dsimp [riskProcess] at hSolv
    linarith only [hSolv]
  have hDb : D b ω ≤ rightLimit D b ω :=
    dividendStrategy_le_rightLimit D hStrategy ω b
  have hAfter : 0 ≤ x + X.X b ω - D b ω := by
    linarith only [hCover, hDb]
  have hOrder :
      x + X.X b ω - D b ω ≤
        x + X.X b ω - rightLimit D a ω := by
    linarith only [hAB]
  have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    (x + X.X b ω - D b ω)
    (x + X.X b ω - rightLimit D a ω) hAfter hOrder
  have hMass :
      (dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ))).toReal =
        D b ω - rightLimit D a ω := by
    rw [avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
      D hStrategy ω a b hab,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hAB)]
  linarith only [hSec, hMass]
