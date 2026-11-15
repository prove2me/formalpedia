-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb43_original_finitecap_C1_zero_reserve_plateau_trueT_compensated_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:34:43.627363+00:00
-- url     : https://prove2.me/submissions/6708e200-f6ca-43ee-b004-678d7a566ca1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
import Theorems.Thm_AvramDividend_Classical_avram_bvb31_original_discounted_drift_volume_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_zero_reserve_discounted_drift_compensator_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hReserveZero : ∀ t : ℝ≥0, t ≤ T →
      riskProcess X x D t ω = 0)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        X.drift * ((b : ℝ) - (a : ℝ))) :
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp ((-q) * (T : ℝ)) * w 0 ≤
    w 0 -
      (∫ z in Iio (0 : ℝ),
        w ((0 : ℝ) + z) - w 0 ∂X.ν) *
      (∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t))  := by
  have hd : 0 ≤ X.drift :=
    (bv_standing_drift_pos X hX hBV).1.le
  have hCash :=
    avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
      X x C D hD ω T 0 hd
      hReserveZero hNoAtom hSourceLine
      (fun t : ℝ => ENNReal.ofReal (Real.exp ((-q) * t)))
  have hConv :=
    avram_bvb31_original_discounted_drift_volume_lintegral_toReal
      X.drift q (T : ℝ) hd hq T.coe_nonneg
  have hBudget :=
    avram_bvb28_original_zero_reserve_discounted_drift_compensator_budget
      X hX hBV hFiniteActivity q w C hC hwCont hw0 hwNeg
      hwSmooth hwGen hwGrad hq (T : ℝ) T.coe_nonneg
  rw [hCash, hConv]
  exact hBudget
