-- Prove2me | solution 6 for AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T04:03:16.806278+00:00
-- url     : https://prove2.me/submissions/caa04e44-7f1f-4b96-b180-7cc0a53e509f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_upExit_split_of_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
-- Short factorization for 8fc83520 (killed-exit factor x boundary sup value).
-- Next step vs the checked-in short derivation: drop the unused ScaleFunction
-- import (the proof never mentions W) so the header matches the authoritative
-- preamble plus exactly the used providers. Mathematical content unchanged:
-- standing-only strong-Markov up-exit split factors the barrier dividend value
-- into the killed-exit integral times the at-barrier value; the endpoint
-- identity rewrites the at-barrier value to barrierSupValue. If the split
-- premise is still Open, the honest outcome is SKETCH_ACCEPTED.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
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
        else 0 ∂P) * barrierSupValue X a q := by
  have hSplit := dividendValue_barrierStrategy_upExit_split_of_standing
    X hX q hq a x ha hx0 hxa
  have hSelf := barrierValue_self_eq_barrierSupValue X q a
  rw [hSplit, hSelf]
