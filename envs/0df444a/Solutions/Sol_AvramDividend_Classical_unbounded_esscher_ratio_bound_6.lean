-- Prove2me | solution 6 for AvramDividend.Classical.unbounded_esscher_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:09:25.534461+00:00
-- url     : https://prove2.me/submissions/bb2b1193-406c-461a-97ac-2919626b915e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Mathlib.Algebra.Order.Field.Basic
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
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  obtain ⟨hpos, φ, hφ, hroot, _⟩ :=
    unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv hExit
  refine ⟨φ, hφ, hroot, ?_⟩
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hbound := unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hExit x y hx hxy
  exact (div_le_iff₀ (hpos y hy)).2 hbound
