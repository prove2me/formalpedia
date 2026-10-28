-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:50:30.796757+00:00
-- url     : https://prove2.me/submissions/1469b365-0f78-4b2e-ace3-b4f3171c3c29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

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
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) *
        dividendValue X q a (barrierStrategy X a a) := by
  -- Killed-exit factorisation via the supremum form: the value splits into the
  -- killed-exit integral times the boundary value (Open 8fc83520 gives the
  -- integral-times-supValue form); the boundary value is the supremum value
  -- (Proved 11b589b7). Rewrite-only, closed by rfl.
  -- Principal lemma: barrierStrategy_value_eq_killed_exit_mul_supValue (Open).
  -- Exact unresolved identity: 8fc83520 (Open, direct strong-Markov proof needed).
  rw [AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
    X hX q hq a x ha hx0 hxa,
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a]
