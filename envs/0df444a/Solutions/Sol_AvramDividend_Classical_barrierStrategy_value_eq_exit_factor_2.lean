-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:28:51.301819+00:00
-- url     : https://prove2.me/submissions/d735aab5-3d71-4784-a8d2-58e5945c9a43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

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
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q := by
  -- Strong-Markov factorisation at the first upcrossing: the value splits into
  -- the killed-exit integral times the boundary value (2f4d50d7, Open); the
  -- integral is the exit identity (3e1ce2c8, SKETCH_ACCEPTED via 14536) and the
  -- boundary value is the supremum value (Proved 11b589b7). Rewrite-only: no
  -- integral is transcribed, the lemmas' own left-hand sides drive matching.
  -- Principal lemma: barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue.
  -- Exact unresolved identities: 2f4d50d7 (Open, direct Markov proof needed),
  -- 3e1ce2c8 (sketch, frontier: stopped identity 09663d0d).
  rw [AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
    X hX q hq a x ha hx0 hxa,
    AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
    X hX q hq W hW a x ha hx0 hxa,
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a]
