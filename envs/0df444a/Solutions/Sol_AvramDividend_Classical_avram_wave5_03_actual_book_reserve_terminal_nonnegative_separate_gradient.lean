-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:58:19.668284+00:00
-- url     : https://prove2.me/submissions/9420fed8-a72c-4d98-a3e5-987105794dca

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original pre-payment risk reserve has nonnegative HJB value even
    when the random clock equals ruin, without a universal positivity claim. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (riskProcess X x D t ω) := by
  let y : ℝ := riskProcess X x D t ω
  change 0 ≤ w y
  have hcap : ENNReal.ofReal y ≤ C := by
    by_cases hzero : t = 0
    · subst t
      have hs : IsDividendStrategy 𝓕 D := hD.1.1
      have hD0 : D 0 ω = 0 := hs.1 ω
      have hX0 : X.X 0 ω = 0 := X.X_zero ω
      simpa only [y, riskProcess, hX0, hD0, sub_zero, add_zero] using hxc
    · have htpos : 0 < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm hzero)
      exact hD.2 ω t htpos
  by_cases hy : 0 ≤ y
  · have hs : y - 0 ≤ w y - w 0 := by
      by_cases hBV : X.BoundedVariation
      · exact avram_wave3_03_bv_full_cap_gradient_secant
          C hC w hw_cont (hw_smooth.2 hBV) hw_grad 0 y
          (le_refl (0 : ℝ)) hy hcap
      · exact avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
          C w hw_cont (hw_smooth.1 hBV) hw_grad 0 y
          (le_refl (0 : ℝ)) hy hcap
    linarith
  · have hneg : y < 0 := lt_of_not_ge hy
    simp [hw_neg y hneg]
