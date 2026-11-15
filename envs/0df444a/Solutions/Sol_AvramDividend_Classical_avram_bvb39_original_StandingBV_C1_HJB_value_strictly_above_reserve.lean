-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb39_original_StandingBV_C1_HJB_value_strictly_above_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:25:04.056918+00:00
-- url     : https://prove2.me/submissions/c31e0531-98a3-42fe-a60b-6c24ba0f3667

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb26_standing_original_BV_HJB_strict_positive_origin
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_global_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → y < w y  := by
  have hOrigin : 0 < w 0 :=
    avram_bvb26_standing_original_BV_HJB_strict_positive_origin
      X hStanding hBV q hq w C hC hwCont hw0 hwNeg
      hwSmooth hwGen hwGrad
  have hSec :=
    avram_p3_bv_finite_cap_linear_global_secant
      C hC hFinite w hwCont hwSmooth hwGrad
  intro y hy0 hyC
  have h0C : (0 : ℝ) ≤ C.toReal := le_trans hy0 hyC
  have h := hSec 0 y (le_refl (0 : ℝ)) hy0
  dsimp only at h
  rw [if_pos hyC, if_pos h0C] at h
  linarith
