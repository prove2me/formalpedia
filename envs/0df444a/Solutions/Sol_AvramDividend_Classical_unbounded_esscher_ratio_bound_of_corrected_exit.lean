-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_ratio_bound_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:15:54.651137+00:00
-- url     : https://prove2.me/submissions/357eaccc-0ba7-4e7c-bfbc-1333024886c9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Corrected killed exits give a positive Cramér root and the ratio decay bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by
  obtain ⟨hpos, φ, hφ, hroot, _⟩ :=
    unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv hExit
  refine ⟨φ, hφ, hroot, ?_⟩
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hbound := unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hExit x y hx hxy
  exact (div_le_iff₀ (hpos y hy)).2 hbound
