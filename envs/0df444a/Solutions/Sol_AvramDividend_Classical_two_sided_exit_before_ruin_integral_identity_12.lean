-- Prove2me | solution 12 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T03:09:11.223869+00:00
-- url     : https://prove2.me/submissions/b83be908-0ebc-4e72-9b26-d7d995d3ac31

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
  -- Repair of CE 14810 (E01 unsolved-goals + E02 rewrite-pattern-absent).
  -- Cause-linked change: the 14810 bridge `hlin` (inline lintegral =
  -- preamble `twoSidedExitExpectation`) never closes cleanly — the `if`
  -- DecidableLT instance keeps one side in named Up/DownTime form — and the
  -- subsequent `rw [← hlin]` finds no expectation-pattern in an already-inline
  -- goal. This repair removes the bridge entirely: the goal is already the
  -- inline lintegral, so the stopped-scale balance applies directly and the
  -- division is done inline with pinned ENNReal algebra.
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  -- Stopped-scale balance in inline form (Open 09663d0d, sketch premise).
  have hBal :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) :=
    AvramDividend.Classical.two_sided_exit_stopped_scale_identity
      X hX q hq W hW a x ha hx0 hxa
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
      ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
    calc
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
          ((∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a)) /
            ENNReal.ofReal (W a) := by
              symm
              exact ENNReal.mul_div_cancel_right hden0 hdenTop
      _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by rw [hBal]
  simpa only [ENNReal.ofReal_div_of_pos hWa] using hdiv
