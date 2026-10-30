-- Prove2me | solution 9 for AvramDividend.Classical.two_sided_exit_stopped_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:06:03.579365+00:00
-- url     : https://prove2.me/submissions/dd31a659-b967-4924-962a-1c8899f0294f

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

-- 09663d0d via BV/UBV case split (v4, 2026-10-28): BV leg closes through the
-- Open bounded-variation stopped balance 2bb529c8; UBV leg closes through the
-- Open unbounded identity aed50a34. V4 restructures binders/comments for a
-- fresh exact-source identity; same cause-linked split as v3.
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
  by_cases hBv : X.BoundedVariation
  · have hBvResult :=
      AvramDividend.Classical.bounded_variation_stopped_scale_balance
        X hX q hq W hW hBv a x ha hx0 hxa
    exact hBvResult
  · have hUbvResult :=
      AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
        X q hq W hW hBv a x ha hx0 hxa
    exact hUbvResult
