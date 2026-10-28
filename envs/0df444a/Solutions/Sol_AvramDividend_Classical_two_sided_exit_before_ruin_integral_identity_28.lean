-- Prove2me | solution 28 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:20:06.527434+00:00
-- url     : https://prove2.me/submissions/7ea6e4a3-ecdb-48e9-8858-f1ff3fae2288
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- SKETCH B for 3e1ce2c8 (parent: none; fresh sorry-free reduction over Open children).
-- Cause-linked vs draft A: hBalance sorry replaced by by_cases split into the
-- two Open stopped-balance legs (BV 2bb529c8, UBV aed50a34); ratio passage via
-- Proved 81ce0d81; fold via unfold + rfl (same (a-x,-x) barriers, as in 16528).
-- No simp-with-BV, no cross-barrier rfl, no W x = W 0 reuse.
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

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
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
  have hFold : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = twoSidedExitExpectation X q a x := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  rw [hFold]
  by_cases hBV : X.BoundedVariation
  · have hBal := AvramDividend.Classical.bounded_variation_stopped_scale_balance
      X hX q hq W hW hBV a x ha hx0 hxa
    rw [hFold] at hBal
    exact AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW a x ha hx0 hxa hBal
  · have hBal :=
      AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
        X q hq W hW hBV a x ha hx0 hxa
    rw [hFold] at hBal
    exact AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW a x ha hx0 hxa hBal
