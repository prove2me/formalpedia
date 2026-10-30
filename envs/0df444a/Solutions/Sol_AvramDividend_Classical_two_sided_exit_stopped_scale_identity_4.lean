-- Prove2me | solution 4 for AvramDividend.Classical.two_sided_exit_stopped_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T05:47:32.843228+00:00
-- url     : https://prove2.me/submissions/8f833a36-6973-4fcd-801d-c66889519208

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
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

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
  have hWapos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWane : ENNReal.ofReal (W a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hWapos
  have hWtop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (W x / W a) =
      ENNReal.ofReal (W x) / ENNReal.ofReal (W a) :=
    ENNReal.ofReal_div_of_pos hWapos
  -- Cause-linked repair vs CE 14817 E01: `simp only [...]` left the
  -- `twoSidedExitUpTime/DownTime` wrappers folded (unsolved `raw = folded`
  -- lintegral goal at L53). The raw iInf clocks match the exact published
  -- definition bodies in `AvramDividend_Classical_TwoSidedExit`
  -- (a151e213: UpTime b = ⨅ t (_ : b < X.X t), DownTime b = ⨅ t (_ : X.X t < b);
  -- Expectation = lintegral of `if up < down`). Hence the identification is
  -- definitional; close by `rfl` instead of the fragile simp-only bridge.
  have hfold : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = twoSidedExitExpectation X q a x :=
    rfl
  by_cases hBV : X.BoundedVariation
  · have h1 :=
      AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
        X hX q hq W hW hBV a x ha hx0 hxa
    rw [hfold, h1, hsplit]
    exact ENNReal.div_mul_cancel hWane hWtop
  · have h2 :=
      AvramDividend.Classical.unbounded_corrected_exit_scale_identity
        X q hq W hW hBV a x ha hx0 hxa
    have h3 :=
      AvramDividend.Classical.chat04_twoSidedExitExpectation_eq_corrected X q a x
    rw [hfold, h3, h2, hsplit]
    exact ENNReal.div_mul_cancel hWane hWtop
