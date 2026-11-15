-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb33_original_finitecap_BV_full_boundary_generator_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:16:07.474685+00:00
-- url     : https://prove2.me/submissions/c3a15527-f9f2-4d19-be31-332fd628a59f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite_activity_closed_cap_generator_HJB
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
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
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
    ∀ y : ℝ, y = 0 ∨ y = C.toReal →
      X.drift +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
        q * w y ≤ 0  := by
  have hZero :=
    avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
      X hStanding hBV hActivity q w C hC hwCont hw0 hwNeg
      hwSmooth hwGen hwGrad
  have hCap :=
    avram_bv_finite_activity_closed_cap_generator_HJB
      X hStanding hBV hActivity q w C hC hFinite
      hwCont hwNeg hwGen hwGrad
  intro y hEnds
  rcases hEnds with h0 | hC'
  · subst y
    linarith
  · subst y
    exact hCap
