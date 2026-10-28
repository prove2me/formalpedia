-- Prove2me | solution 2 for AvramDividend.Classical.two_sided_exit_stopped_scale_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:43:37.46098+00:00
-- url     : https://prove2.me/submissions/76933506-37bc-4f11-b200-14c04cbffb74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_bounded_variation_two_sided_exit_before_ruin_identity
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

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
  classical
  have hratio : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W a) := by
    change twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)
    by_cases hBV : X.BoundedVariation
    · exact bounded_variation_two_sided_exit_before_ruin_identity
        X hX q hq W hW hBV a x ha hx0 hxa
    · rw [chat04_twoSidedExitExpectation_eq_corrected X q a x]
      exact unbounded_corrected_exit_scale_identity
        X q hq W hW hBV a x ha hx0 hxa
  by_cases hzero : W a = 0
  · have hmono : W x ≤ W a :=
      hW.2.2.2.1 hx0 (le_of_lt ha) hxa
    have hxzero : W x = 0 :=
      le_antisymm (by simpa [hzero] using hmono) (hW.2.1 x hx0)
    simp [hratio, hzero, hxzero]
  · have hWa_nonneg : 0 ≤ W a := hW.2.1 a (le_of_lt ha)
    have hWa_pos : 0 < W a := lt_of_le_of_ne hWa_nonneg (Ne.symm hzero)
    rw [hratio]
    rw [← ENNReal.ofReal_mul (div_nonneg (hW.2.1 x hx0) (le_of_lt hWa_pos))]
    congr 1
    field_simp [ne_of_gt hWa_pos]
