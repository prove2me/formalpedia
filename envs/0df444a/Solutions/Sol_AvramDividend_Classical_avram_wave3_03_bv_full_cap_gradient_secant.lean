-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_full_cap_gradient_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:57:27.582212+00:00
-- url     : https://prove2.me/submissions/df324751-40f8-4f7c-b9b9-2163d0dc068b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b ≤ C) :
    b - a ≤ w b - w a := by
  have hsub : interior (Icc a b) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have hyI : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    have hy0 : 0 < y := lt_of_le_of_lt ha hyI.1
    have hyb : ENNReal.ofReal y < ENNReal.ofReal b :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy0.le).2 hyI.2
    exact ⟨hy0, lt_of_lt_of_le hyb hb⟩
  have hcontinuity : ContinuousOn w (Icc a b) := by
    apply hw_cont.mono
    intro y hy
    exact ha.trans hy.1
  have hdiff : DifferentiableOn ℝ w (interior (Icc a b)) :=
    hw_smooth.differentiableOn_one.mono hsub
  have hderiv : ∀ y ∈ interior (Icc a b), (1 : ℝ) ≤ deriv w y := by
    intro y hy
    exact hw_grad y (hsub hy).1 (hsub hy).2
  have hsec := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hcontinuity hdiff hderiv a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  simpa only [one_mul] using hsec
