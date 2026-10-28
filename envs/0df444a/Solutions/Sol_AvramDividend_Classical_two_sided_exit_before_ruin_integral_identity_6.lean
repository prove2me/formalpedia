-- Prove2me | solution 6 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:57:13.192826+00:00
-- url     : https://prove2.me/submissions/46550c8d-f3f8-4fd1-8f55-f78eace5ef2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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

-- Reduction: the integral identity is the stopped q-scale identity
-- (09663d0d, Open child) divided by the strictly positive value W a
-- (Proved: scaleFunction_strict_pos_of_standing). Principal lemma:
-- two_sided_exit_stopped_scale_identity. Exact unresolved identity (parent):
-- none at this level; the stopped identity itself remains Open and is the
-- coordinator-owned frontier obligation.

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
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hmul :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) :=
    AvramDividend.Classical.two_sided_exit_stopped_scale_identity
      X hX q hq W hW a x ha hx0 hxa
  have hA0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos).2 hWa)
  have hAtop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hdiv := congrArg
    (fun z : ℝ≥0∞ => z / ENNReal.ofReal (W a)) hmul
  rw [ENNReal.mul_div_cancel_right hA0 hAtop] at hdiv
  calc
    (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
        ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := hdiv
    _ = ENNReal.ofReal (W x / W a) :=
      (ENNReal.ofReal_div_of_pos hWa).symm
