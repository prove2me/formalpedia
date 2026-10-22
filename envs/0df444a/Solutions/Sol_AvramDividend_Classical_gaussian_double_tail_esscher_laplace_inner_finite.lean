-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_esscher_laplace_inner_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:38:35.792817+00:00
-- url     : https://prove2.me/submissions/bc275078-c1e0-4246-82a4-f8f0ca25b33d

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_finite
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Positive Laplace parameter yields finiteness of the unweighted double-tail integral. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume) < ⊤ := by
  let I : ENNReal :=
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume)
  have hprod :=
    gaussian_double_tail_esscher_laplace_finite μ φ θ hφ hθ.le hlevy
  change ENNReal.ofReal (θ ^ 2) * I < ⊤ at hprod
  have hcoef : 0 < ENNReal.ofReal (θ ^ 2) :=
    ENNReal.ofReal_pos.mpr (pow_pos hθ 2)
  have hfin : I < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.mp hprod with ⟨_, hi⟩ | hzero | hzero
    · exact hi
    · exact False.elim ((ne_of_gt hcoef) hzero)
    · simp [hzero]
  exact hfin
