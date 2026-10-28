-- Prove2me | solution 7 for AvramDividend.Classical.two_sided_exit_stopped_scale_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:49:47.227521+00:00
-- url     : https://prove2.me/submissions/b9bc6680-7882-4d12-8f4a-c62850bdf09f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bounded_variation_two_sided_exit_before_ruin_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  have hRatio : twoSidedExitExpectation X q a x =
      ENNReal.ofReal (W x / W a) := by
    rcases Classical.em (X.BoundedVariation) with hBV | hnbv
    · exact AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
        X hX q hq W hW hBV a x ha hx0 hxa
    · have hCorr :=
        AvramDividend.Classical.unbounded_corrected_exit_scale_identity
          X q hq W hW hnbv a x ha hx0 hxa
      have hEq :=
        AvramDividend.Classical.chat04_twoSidedExitExpectation_eq_corrected
          X q a x
      rw [hEq]
      exact hCorr
  have hUnfold : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = twoSidedExitExpectation X q a x := by
    simp only [AvramDividend.Classical.twoSidedExitExpectation,
      AvramDividend.Classical.twoSidedExitUpTime,
      AvramDividend.Classical.twoSidedExitDownTime]
    apply lintegral_congr
    intro ω
    by_cases h : (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞))
    · simp [h]
    · simp [h]
  have hExp : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W a) := by
    rw [hUnfold]
    exact hRatio
  have hPos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  obtain ⟨_, hWnn, _, _, _⟩ := hW
  have hWx : 0 ≤ W x := hWnn x hx0
  have hWa_ne : W a ≠ 0 := ne_of_gt hPos
  have hAlg : W x / W a * W a = W x := div_mul_cancel₀ _ hWa_ne
  calc (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a)
      = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a) := by rw [hExp]
    _ = ENNReal.ofReal (W x / W a * W a) :=
        (ENNReal.ofReal_mul (div_nonneg hWx hPos.le)).symm
    _ = ENNReal.ofReal (W x) := by rw [hAlg]
