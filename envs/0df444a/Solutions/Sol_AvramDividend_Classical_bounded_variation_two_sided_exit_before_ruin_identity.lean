-- Prove2me | solution 1 for AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T00:20:00.582911+00:00
-- url     : https://prove2.me/submissions/fd6dc7c8-976f-497f-b062-08c4c53c7e50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- 494dbcd1 via published helper 2bb529c8 (replaces cyclic parent import).
Helper identity authoritative: publication job 54892a26 PUBLISHED; theorem_id
2bb529c8-d611-4c49-9460-1d4af4620ae8, name AvramDividend.Classical.
bounded_variation_stopped_scale_balance, status Open. Module mapping follows the
repo-wide Theorems.Thm_<dotted_name_underscored> convention evidenced by every
sibling import; remote lint-submit admission is the authority (safe reject on
mismatch). hBV discharged from the target context. Revision 2 (repair of CE 14803 E01): `ENNReal.eq_div_iff` expects
`c * a = b` (divisor on the left) but `hstop` states `a * c = b`; single
cause-linked change `rw [mul_comm] at hstop` before the exact step, as
prescribed in the sibling proof plan. No local Lean was run.
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
      else 0 ∂P) = twoSidedExitExpectation X q a x := rfl
  rw [← hfold, hsplit]
  rw [mul_comm] at hstop
  exact (ENNReal.eq_div_iff hWane hWtop).mpr hstop
