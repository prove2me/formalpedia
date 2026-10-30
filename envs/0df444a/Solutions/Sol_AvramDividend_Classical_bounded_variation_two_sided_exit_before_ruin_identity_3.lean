-- Prove2me | solution 3 for AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T03:17:06.801285+00:00
-- url     : https://prove2.me/submissions/d307e6b3-f836-4da4-9a32-ddbfa5475259

/- 494dbcd1 repair of CE 14807 (unsolved goals at hfold rfl).
Cause: `hfold ... := rfl` claimed definitional equality between the raw
inline-iInf integral and `twoSidedExitExpectation`, but the target wraps the
passage times in named defs `twoSidedExitUpTime`/`twoSidedExitDownTime`, so
`rfl` alone does not unfold them. Single cause-linked change: unfold the
three defs before `rfl`. Keeps the verified `mul_comm` fix for
`ENNReal.eq_div_iff` (needs `ofReal W a * integral = ofReal W x`).
Conditional: depends on Open `bounded_variation_stopped_scale_balance`
(`2bb529c8`); sketch-grade, expects SKETCH_ACCEPTED, not a complete proof.
No local Lean was run.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by
  have hWapos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hstop : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) :=
    AvramDividend.Classical.bounded_variation_stopped_scale_balance X hX q hq W hW hBV a x ha hx0 hxa
  have hWane : ENNReal.ofReal (W a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hWapos
  have hWtop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (W x / W a) =
      ENNReal.ofReal (W x) / ENNReal.ofReal (W a) :=
    ENNReal.ofReal_div_of_pos hWapos
  have hfold : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = twoSidedExitExpectation X q a x := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  rw [← hfold, hsplit]
  rw [mul_comm] at hstop
  exact (ENNReal.eq_div_iff hWane hWtop).mpr hstop
