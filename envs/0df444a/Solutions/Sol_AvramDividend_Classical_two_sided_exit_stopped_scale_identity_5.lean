-- Prove2me | solution 5 for AvramDividend.Classical.two_sided_exit_stopped_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:00:52.541815+00:00
-- url     : https://prove2.me/submissions/ad15ad6e-a668-4274-ac20-60280f885dd2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity

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
  by_cases hBV : X.BoundedVariation
  · exact AvramDividend.Classical.bounded_variation_stopped_scale_balance
      X hX q hq W hW hBV a x ha hx0 hxa
  · exact AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hBV a x ha hx0 hxa
