-- Prove2me | solution 16 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:46:36.845139+00:00
-- url     : https://prove2.me/submissions/3c2a08b2-39d6-4ed0-bec6-236ad8fefb73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by
  -- Proposition 1 assembly: exit-factor split (sketch 870df5c1, SKETCH_ACCEPTED
  -- via 14551), supremum value as scale ratio (Open a8d4c941), and the ENNReal
  -- scale-ratio cancellation (Proved 5aaab3d9) with strict positivity of W
  -- (Proved) and of its derivative (Open scaleDeriv_pos).
  -- Principal lemma: barrierStrategy_value_eq_exit_factor.
  -- Exact unresolved identities: 2f4d50d7 (inside exit-factor sketch),
  -- a8d4c941 (supValue ratio), 4052a131 (deriv positivity).
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hd : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos X hX q hq W hW a ha
  have hexit : dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
      X hX q hq W hW a ha x hx0 hxa
  have hsup : barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  have hprod : ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a)
      = ENNReal.ofReal (W x / deriv W a) :=
    AvramDividend.Classical.ennreal_scale_ratio_cancel (W x) (W a) (deriv W a)
      hWx hWa hd
  calc dividendValue X q x (barrierStrategy X x a)
      = ENNReal.ofReal (W x / W a) * barrierSupValue X a q := hexit
    _ = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a) := by
        rw [hsup]
    _ = ENNReal.ofReal (W x / deriv W a) := hprod
