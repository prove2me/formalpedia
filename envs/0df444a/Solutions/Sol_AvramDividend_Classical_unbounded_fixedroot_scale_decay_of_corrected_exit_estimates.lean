-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:46:14.971036+00:00
-- url     : https://prove2.me/submissions/dd34b324-c047-410b-9131-9a52a70ddc93

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hpos : ∀ y : ℝ, 0 < y → 0 < W y)
    (φ : ℝ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x ≤
        ENNReal.ofReal (Real.exp (-(φ * (a - x))))) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hle : ENNReal.ofReal (W x / W y) ≤
      ENNReal.ofReal (Real.exp (-(φ * (y - x)))) := by
    rw [← hExit y x hy hx.le hxy]
    exact hBound y x hy hx.le hxy
  have hr : W x / W y ≤ Real.exp (-(φ * (y - x))) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hle
  exact (div_le_iff₀ (hpos y hy)).mp hr
