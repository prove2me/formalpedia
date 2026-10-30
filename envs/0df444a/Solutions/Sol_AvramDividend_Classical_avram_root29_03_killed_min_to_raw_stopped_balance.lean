-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_killed_min_to_raw_stopped_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:11:44.245523+00:00
-- url     : https://prove2.me/submissions/23a77bba-cc9b-432a-b3aa-23a3b75a7470

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_raw_exit_scale_product_eq_stopped_terminal

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Given genuine killed stopped-minimum harmonicity as an explicit premise,
the exact raw strict upper-before-ruin stopped-scale cross-product follows
from a verified original stopped terminal factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled : (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (min (twoSidedExitUpTime X (a - x) ω)
              (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal ω))
      else 0 ∂P) = ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  exact (avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
    X hX q hq W hW a x ha hx0 hxa).trans hKilled
