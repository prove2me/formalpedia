-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb32_original_finitecap_constant_reserve_true_discounted_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:07:17.970518+00:00
-- url     : https://prove2.me/submissions/ca2bdebd-c8a9-4b43-9494-65dd5b1f2de7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
import Theorems.Thm_AvramDividend_Classical_avram_bvb31_original_discounted_drift_volume_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_finitecap_closed_cap_discounted_drift_compensator_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hReserve : ∀ t : ℝ≥0, t ≤ T →
      riskProcess X x D t ω = C.toReal)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T → rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        X.drift * ((b : ℝ) - (a : ℝ))) :
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp ((-q) * (T : ℝ)) * w C.toReal ≤
    w C.toReal -
      (∫ z in Iio (0 : ℝ),
        w (C.toReal + z) - w C.toReal ∂X.ν) *
      (∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t))  := by
  have hd : 0 ≤ X.drift :=
    (bv_standing_drift_pos X hStanding hBV).1.le
  have hCash :=
    avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
      X x C D hD ω T C.toReal hd
      hReserve hNoAtom hSourceLine
      (fun t : ℝ => ENNReal.ofReal (Real.exp ((-q) * t)))
  have hConv :=
    avram_bvb31_original_discounted_drift_volume_lintegral_toReal
      X.drift q (T : ℝ) hd hq T.coe_nonneg
  have hBudget :=
    avram_bvb27_original_finitecap_closed_cap_discounted_drift_compensator_budget
      X hStanding hBV hActivity q w C hC hFinite
      hwCont hwNeg hwGen hwGrad hq (T : ℝ) T.coe_nonneg
  rw [hCash, hConv]
  exact hBudget
