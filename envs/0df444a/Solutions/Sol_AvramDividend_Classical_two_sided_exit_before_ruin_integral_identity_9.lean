-- Prove2me | solution 9 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:24:04.275835+00:00
-- url     : https://prove2.me/submissions/210a102d-9c0c-4821-a620-01c8cfec036a

/-
Repair of candidate 14763 (remote CE E01 at L9: invalid 'import'
command -- the leading module-docstring opener above the imports is itself a
command, so imports must follow it. Single cause-linked change: this header
is now a plain block comment placed where it is, leaving all imports at the
top before any command. No tactic change.

Repair of candidate 14750 (remote CE E01 at L48: application type mismatch).
`hstop` states `lintegral * ofReal (W a) = ofReal (W x)` but
`(ENNReal.eq_div_iff hWane hWtop).mpr` expects `ofReal (W a) * lintegral`.
Single cause-linked change: `rw [mul_comm] at hstop` before the exact step.
Still a conditional reduction onto Open `09663d0d` (stopped-scale identity);
not a proved root. No local Lean was run.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
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
    AvramDividend.Classical.two_sided_exit_stopped_scale_identity X hX q hq W hW a x ha hx0 hxa
  have hWane : ENNReal.ofReal (W a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hWapos
  have hWtop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (W x / W a) =
      ENNReal.ofReal (W x) / ENNReal.ofReal (W a) :=
    ENNReal.ofReal_div_of_pos hWapos
  rw [hsplit]
  -- `ENNReal.eq_div_iff` needs `c * a = b`, i.e. `ofReal (W a)` on the left;
  -- `hstop` has the factors in the opposite order (14750 E01). Commute once.
  rw [mul_comm] at hstop
  exact (ENNReal.eq_div_iff hWane hWtop).mpr hstop
