-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb34_original_finitecap_BV_allclosed_physical_generator_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:19:38.489855+00:00
-- url     : https://prove2.me/submissions/a4c8cf7a-7952-41d3-83ca-5729e918ef78

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb33_original_finitecap_BV_full_boundary_generator_sign
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal →
      X.drift * (if y = 0 ∨ y = C.toReal then 1 else deriv w y) +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
        q * w y ≤ 0  := by
  have hBoundary :=
    avram_bvb33_original_finitecap_BV_full_boundary_generator_sign
      X hStanding hBV hActivity q w C hC hFinite
      hwCont hw0 hwNeg hwSmooth hwGen hwGrad
  intro y hy0 hyC
  by_cases hEnd : y = 0 ∨ y = C.toReal
  · simpa only [if_pos hEnd, mul_one] using hBoundary y hEnd
  · have hn0 : y ≠ 0 := fun h => hEnd (Or.inl h)
    have hnC : y ≠ C.toReal := fun h => hEnd (Or.inr h)
    have hPos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hn0)
    have hLt : y < C.toReal := lt_of_le_of_ne hyC hnC
    have hyIn : ENNReal.ofReal y < C :=
      (ENNReal.ofReal_lt_iff_lt_toReal hPos.le hFinite).2 hLt
    have hG := (hwGen y hPos hyIn).2
    have hRep :=
      boundedVariation_generator_physical_drift_representation
        X hBV w y (hwGen y hPos hyIn).1
    rw [hRep] at hG
    simpa only [if_neg hEnd] using hG
