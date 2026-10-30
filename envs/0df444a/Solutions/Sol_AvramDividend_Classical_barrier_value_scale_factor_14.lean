-- Prove2me | solution 14 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:55:45.306571+00:00
-- url     : https://prove2.me/submissions/a036b19d-7b53-476d-a0d6-733f440e5ad8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Scale-factor split via Proved positivity + Open exit factor + Proved self bridge.
-- Variant t (2026-10-29): top-level rewrite architecture over prior calc file.
-- hWa grounds 0 < W a (Proved 59531c77); hfac_x gives divVal x = ratio * supValue
-- (Open 870df5c1); hself gives divVal a = supValue (Proved 11b589b7).
-- `rw [hfac_x]` then `rw [<-hself]` closes the right conjunct; no calc block.
-- Mathematics unchanged; elaboration strictly more explicit.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := by
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hfac_x :
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
      X hX q hq W hW a ha x hx0 hxa
  have hself :
      dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  refine ⟨hWa, ?_⟩
  rw [hfac_x]
  rw [← hself]
