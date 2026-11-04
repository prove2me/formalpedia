-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:59:18.762061+00:00
-- url     : https://prove2.me/submissions/d8015c2f-f580-4ca8-9857-a091053dccda

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine original payment time carries the full Stieltjes source-frozen cell inequality. -/
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
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPay : (b : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by
  have hEligible : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω := by
    rcases avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
        X x D ω (b : ℝ) hPay with h0 | ⟨_, hb⟩
    · left
      simpa using h0
    · right
      simpa using hb
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hSolv := hD.1.2 ω b hEligible
  have hCover : rightLimit D b ω ≤ x + X.X b ω := by
    dsimp [riskProcess] at hSolv
    linarith only [hSolv]
  have hMon : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hStrategy ω) hab
  have hAfter : 0 ≤ x + X.X b ω - rightLimit D b ω := by
    linarith only [hCover]
  have hOrder :
      x + X.X b ω - rightLimit D b ω ≤
      x + X.X b ω - rightLimit D a ω := by
    linarith only [hMon]
  have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    (x + X.X b ω - rightLimit D b ω)
    (x + X.X b ω - rightLimit D a ω) hAfter hOrder
  have hMass :
      (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal =
        rightLimit D b ω - rightLimit D a ω := by
    rw [dividendMeasure_Ioc_rightLimit D hStrategy ω a b,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hMon)]
  linarith only [hSec, hMass]