-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_weighted_double_tail_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:06:54.443638+00:00
-- url     : https://prove2.me/submissions/b526fdf1-261a-4194-88f9-be23fcfd1410

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_antitone_positive
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ β w : ℝ)
    (hφ : 0 < φ) (hw : 0 ≤ w)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    AntitoneOn (fun t : ℝ =>
      Real.exp (-w * t) *
        (|β| + (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ).toReal))
      (Ioi (0 : ℝ)) := by
  let K : ℝ → ℝ := fun t : ℝ =>
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ).toReal
  have hanti : AntitoneOn K (Ioi (0 : ℝ)) :=
    gaussian_double_tail_real_kernel_antitone_positive μ φ hφ hlevy
  have hnonneg : ∀ t : ℝ, 0 < t → 0 ≤ K t := by
    intro t ht
    exact ENNReal.toReal_nonneg
  exact causal_weighted_antitone_kernel K β w hw hanti hnonneg
