-- Prove2me | solution 1 for AvramDividend.Classical.chat12_lower_eventual_renewal_of_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:06:55.884584+00:00
-- url     : https://prove2.me/submissions/7d74c82a-3850-46c1-a433-7652909be009

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_actual_grid
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_pos_eventually_backward_scale_gap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hderiv : 0 ≤ deriv W a :=
    scaleFunction_deriv_nonneg X q W hW a ha
  have hdpos : 0 < deriv W a :=
    lt_of_le_of_ne hderiv (Ne.symm hd)
  have hgap : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < W a - W (a - ε) :=
    hasDerivAt_pos_eventually_backward_scale_gap W a (deriv W a) hD hdpos
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < a := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds ha)
  have hpositive : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  filter_upwards [hgap, hsmall, hpositive, hExit] with ε hgapε hεa hε hExitε
  have hWleft : 0 ≤ W (a - ε) :=
    hW.2.1 (a - ε) (by linarith)
  have hWinc : W (a - ε) < W a := by
    linarith
  apply barrierSupValue_ge_left_scale_quotient_of_actual_grid
    X W a q ε (le_of_lt hq) hε hWa hWleft hWinc
  exact killed_firstRecord_grid_expected_scale_lower_of_strict_exit
    X hX q hq W hW a ε ha hε hεa hWa hWleft hWinc hExitε
