-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb44_original_finitecap_C1_any_constant_reserve_fullT_compensated_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:37:38.861955+00:00
-- url     : https://prove2.me/submissions/4a98c4dd-a53d-49f8-aa1e-44e28e179546

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb41_original_finitecap_positive_constant_reserve_discounted_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_bvb43_original_finitecap_C1_zero_reserve_plateau_trueT_compensated_cash
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
    (hwCont : ContinuousOn w (Ici (0 : ℝ))) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) (r : ℝ)
    (hr0 : 0 ≤ r) (hrC : r ≤ C.toReal)
    (hReserve : ∀ t : ℝ≥0, t ≤ T →
      riskProcess X x D t ω = r)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T → rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        X.drift * ((b : ℝ) - (a : ℝ))) :
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp ((-q) * (T : ℝ)) * w r ≤
    w r -
      (∫ z in Iio (0 : ℝ),
        w (r + z) - w r ∂X.ν) *
      (∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t))  := by
  by_cases hr : r = 0
  · subst r
    exact
      avram_bvb43_original_finitecap_C1_zero_reserve_plateau_trueT_compensated_cash
        X hStanding hBV hActivity q hq w C hC hwCont hw0 hwNeg
        hwSmooth hwGen hwGrad x D hD ω T hReserve hNoAtom hSourceLine
  · have hrPos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    exact
      avram_bvb41_original_finitecap_positive_constant_reserve_discounted_cash_budget
        X hStanding hBV hActivity q hq w C hC hFinite hwCont hwNeg
        hwGen hwGrad x D hD ω T r hr0 hrC hrPos
        hReserve hNoAtom hSourceLine
