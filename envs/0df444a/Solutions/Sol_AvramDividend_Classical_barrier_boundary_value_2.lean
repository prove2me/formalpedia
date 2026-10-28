-- Prove2me | solution 2 for AvramDividend.Classical.barrier_boundary_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:58:40.646107+00:00
-- url     : https://prove2.me/submissions/3c038bf6-d6da-4284-a668-1475c6c525d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    dividendValue X q a (barrierStrategy X a a) = ENNReal.ofReal (W a / deriv W a) := by
  -- Boundary value via the supremum value: the value at a equals the running
  -- supremum value (Proved 11b589b7), which is the scale ratio (Open a8d4c941,
  -- history-backed module). Twin of the f9580183 attempt, which was refused at
  -- admission on its ReflectionCapital preamble import; this record carries the
  -- clean preamble. Principal lemma: barrierValue_self_eq_barrierSupValue.
  -- Exact unresolved identity: supValue scale ratio a8d4c941 (Open).
  have hsup : barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  have hself : dividendValue X q a (barrierStrategy X a a) =
      barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  rw [hself, hsup]
