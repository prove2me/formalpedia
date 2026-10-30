-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_barrierSupValue_finite_of_esscher_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:38:50.903895+00:00
-- url     : https://prove2.me/submissions/79514e0b-ed0c-434a-baaf-2630bfc13acc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_finite_of_trueExit_factor
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original killed reflected-regulator boundary dividend reward is finite
whenever a positive Esscher root exists, independently of q-scale exit laws. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q < ∞ := by
  let ε : ℝ := a
  have hε : 0 < ε := ha
  let p : ℝ≥0∞ := twoSidedExitExpectation X q (a + ε) a
  have hExitBound : p ≤ ENNReal.ofReal (Real.exp (-(φ * ε))) := by
    dsimp [p]
    rw [chat04_twoSidedExitExpectation_eq_corrected X q (a + ε) a]
    have h := corrected_exit_exp_bound_at_positive_root
      X q hq φ hφ hroot (a + ε) a (add_pos ha hε)
      (le_of_lt ha) (le_add_of_nonneg_right hε.le)
    simpa [add_sub_cancel_left] using h
  have hExp : ENNReal.ofReal (Real.exp (-(φ * ε))) < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    exact Real.exp_lt_one_iff.mpr
      (neg_lt_zero.mpr (mul_pos hφ hε))
  have hp1 : p < 1 := lt_of_le_of_lt hExitBound hExp
  have hpTop : p ≠ ⊤ :=
    ne_of_lt (lt_of_lt_of_le hp1 le_top)
  have hpn : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hpReal : p.toReal < 1 := by
    apply ENNReal.ofReal_lt_one.mp
    simpa only [ENNReal.ofReal_toReal hpTop] using hp1
  have hExit :
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) = ENNReal.ofReal p.toReal := by
    simpa only [p, twoSidedExitExpectation, twoSidedExitUpTime,
      twoSidedExitDownTime, add_sub_cancel_left] using
      (ENNReal.ofReal_toReal hpTop).symm
  exact chat12_barrierSupValue_finite_of_trueExit_factor
    X hX q hq a ε ha hε p.toReal hpn hpReal hExit
