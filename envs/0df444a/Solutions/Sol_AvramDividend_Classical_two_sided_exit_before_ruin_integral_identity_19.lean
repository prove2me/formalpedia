-- Prove2me | solution 19 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:08:39.244708+00:00
-- url     : https://prove2.me/submissions/98266a04-e09d-4338-b972-8a730b3f2808
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

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
  -- MATHEMATICAL_DECOMPOSITION: split on BoundedVariation, following the
  -- sketch-guide's first decomposition. Each branch closes through the
  -- Proved bridge `chat04_exit_ratio_of_stopped_balance` (81ce0d81), which
  -- turns a stopped balance `E * W a = W x` into the ratio identity using
  -- Proved positivity of `W a` under Standing (59531c77, used inside 81ce0d81).
  -- Open dependencies (expect SKETCH_ACCEPTED, not full ACCEPTED):
  --   BV branch: `bounded_variation_stopped_scale_balance` (2bb529c8);
  --   unbounded branch: `chat04_unbounded_two_sided_exit_stopped_scale_identity`
  --     (aed50a34, needs no Standing hypothesis).
  -- No self-reference to the catalogue target name; top-level `solution` only.
  rcases Classical.em X.BoundedVariation with hBV | hnbv
  · have hbal :=
      AvramDividend.Classical.bounded_variation_stopped_scale_balance
        X hX q hq W hW hBV a x ha hx0 hxa
    exact AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW a x ha hx0 hxa hbal
  · have hbal :=
      AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
        X q hq W hW hnbv a x ha hx0 hxa
    exact AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW a x ha hx0 hxa hbal
