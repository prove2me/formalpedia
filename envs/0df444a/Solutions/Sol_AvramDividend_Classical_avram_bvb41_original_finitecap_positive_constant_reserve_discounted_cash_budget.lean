-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb41_original_finitecap_positive_constant_reserve_discounted_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:29:50.800612+00:00
-- url     : https://prove2.me/submissions/126c50b4-f67c-4d24-9b19-dcc95d4ecadb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
import Theorems.Thm_AvramDividend_Classical_avram_bvb31_original_discounted_drift_volume_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite_activity_closed_cap_generator_HJB
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
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
    (ω : Ω) (T : ℝ≥0) (r : ℝ)
    (hr0 : 0 ≤ r) (hrC : r ≤ C.toReal)
    (hrPos : 0 < r)
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
  have hd : 0 ≤ X.drift :=
    (bv_standing_drift_pos X hStanding hBV).1.le
  have hCash :=
    avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
      X x C D hD ω T r hd
      hReserve hNoAtom hSourceLine
      (fun t : ℝ => ENNReal.ofReal (Real.exp ((-q) * t)))
  have hConv :=
    avram_bvb31_original_discounted_drift_volume_lintegral_toReal
      X.drift q (T : ℝ) hd hq T.coe_nonneg
  let I : ℝ := ∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t)
  let K : ℝ := ∫ z in Iio (0 : ℝ), w (r + z) - w r ∂X.ν
  let b : ℝ := if r = 0 ∨ r = C.toReal then 1 else deriv w r
  have hCoeff : 1 ≤ b := by
    by_cases hEnd : r = 0 ∨ r = C.toReal
    · simp only [b, if_pos hEnd]
      exact le_refl _
    · have hrNe0 : r ≠ 0 := fun h => hEnd (Or.inl h)
      have hrNeC : r ≠ C.toReal := fun h => hEnd (Or.inr h)
      have hrPos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrNe0)
      have hrLt : r < C.toReal := lt_of_le_of_ne hrC hrNeC
      have hrIn : ENNReal.ofReal r < C :=
        (ENNReal.ofReal_lt_iff_lt_toReal hrPos.le hFinite).2 hrLt
      simpa only [b, if_neg hEnd] using hwGrad r hrPos hrIn
  have hSign0 : X.drift * b + K - q * w r ≤ 0 := by
    by_cases hCap : r = C.toReal
    · subst r
      have hEnd : C.toReal = 0 ∨ C.toReal = C.toReal := Or.inr rfl
      have hCapSign := avram_bv_finite_activity_closed_cap_generator_HJB
          X hStanding hBV hActivity q w C hC hFinite
          hwCont hwNeg hwGen hwGrad
      simpa only [b, K, if_pos hEnd, mul_one] using hCapSign
    · have hrNe0 : r ≠ 0 := ne_of_gt hrPos
      have hrLt : r < C.toReal := lt_of_le_of_ne hrC hCap
      have hrIn : ENNReal.ofReal r < C :=
        (ENNReal.ofReal_lt_iff_lt_toReal hrPos.le hFinite).2 hrLt
      have hGen := (hwGen r hrPos hrIn).2
      have hRep := boundedVariation_generator_physical_drift_representation
          X hBV w r (hwGen r hrPos hrIn).1
      rw [hRep] at hGen
      have hEnd : ¬ (r = 0 ∨ r = C.toReal) := not_or.mpr ⟨hrNe0, hCap⟩
      simpa only [b, K, if_neg hEnd] using hGen
  have hSign : X.drift + K - q * w r ≤ 0 := by
    have hDrop : 0 ≤ X.drift * (b - 1) := mul_nonneg hd (sub_nonneg.mpr hCoeff)
    nlinarith
  have hIntegral : q * I + Real.exp ((-q) * (T : ℝ)) = 1 :=
    avram_bvb23_original_discounted_zero_contact_budget_identity
      q (T : ℝ) hq T.coe_nonneg
  have hExp : Real.exp ((-q) * (T : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hq.le T.coe_nonneg])
  have hINonneg : 0 ≤ I := by nlinarith [hIntegral]
  have hProduct : (X.drift + K - q * w r) * I ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hSign hINonneg
  have hExpEq : Real.exp ((-q) * (T : ℝ)) = 1 - q * I := by linarith [hIntegral]
  have hBudget : X.drift * I +
      Real.exp ((-q) * (T : ℝ)) * w r ≤
        w r - K * I := by
    calc
      X.drift * I + Real.exp ((-q) * (T : ℝ)) * w r =
          (X.drift + K - q * w r) * I + w r - K * I := by
        rw [hExpEq]
        ring
      _ ≤ w r - K * I := by linarith [hProduct]
  rw [hCash, hConv]
  exact hBudget
