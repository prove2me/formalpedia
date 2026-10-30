-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T05:16:25.075715+00:00
-- url     : https://prove2.me/submissions/406e2cdd-d5a8-4ad2-aecd-f526cdc08244

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
  -- Route: strong-Markov splitting of the barrier dividend value at the
  -- up-exit time (principal lemma, currently missing), closed by the Proved
  -- deterministic identification at the barrier level.
  -- On {up-exit strictly before down-exit}, spectral negativity (no positive
  -- jumps) puts the process exactly at level a at the up-exit time, and the
  -- barrier strategy started from x <= a pays nothing before that time; the
  -- remaining discounted dividends equal the value started from a, which is
  -- `barrierSupValue X a q` by the Proved `barrierValue_self_eq_barrierSupValue`.
  -- On the complementary event (down-exit first / ruin), the barrier strategy
  -- pays nothing.
  have hmarkov : dividendValue X q x (barrierStrategy X x a)
      = (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) * dividendValue X q a (barrierStrategy X a a) := by
    -- Discharged by published Open child 79978d61 (W-free split lemma,
    -- PUBLISHED 2026-10-25); honest sketch ceiling while the child is Open.
    exact AvramDividend.Classical.dividendValue_barrierStrategy_upExit_split_of_standing
      X hX q hq a x ha hx0 hxa
  rw [hmarkov, barrierValue_self_eq_barrierSupValue]
