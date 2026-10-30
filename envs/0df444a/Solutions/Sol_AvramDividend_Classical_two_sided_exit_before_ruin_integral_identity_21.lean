-- Prove2me | solution 21 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:49:44.564016+00:00
-- url     : https://prove2.me/submissions/0a2bb44c-97f4-4bfb-b6eb-551b06a03537

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_iff_stopped_balance

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
  have hBridge : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = twoSidedExitExpectation X q a x := by
    -- Repair of CE 15305 E01: simp only unfolds the expectation and the
    -- up/down times in the proposition but leaves folded occurrences inside
    -- the DecidableLT instance arguments; the sides are definitionally equal,
    -- so rfl closes the residual goal.
    simp only [twoSidedExitExpectation, twoSidedExitUpTime, twoSidedExitDownTime]
    rfl
  have hBal := AvramDividend.Classical.two_sided_exit_stopped_scale_identity
    X hX q hq W hW a x ha hx0 hxa
  have hBalWrap : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
    rw [← hBridge]
    exact hBal
  have hIff := AvramDividend.Classical.chat04_exit_ratio_iff_stopped_balance
    X hX q hq W hW a x ha hx0 hxa
  have hRatio : twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) :=
    hIff.mpr hBalWrap
  rw [hBridge]
  exact hRatio
