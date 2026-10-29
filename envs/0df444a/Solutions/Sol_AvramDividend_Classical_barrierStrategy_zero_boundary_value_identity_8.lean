-- Prove2me | solution 8 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:15:55.434675+00:00
-- url     : https://prove2.me/submissions/e2cf4222-b8cd-4965-84e2-b33717974f0f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  -- Repair of CE 14874 (E01: `simp [hval]` made no progress at L26).
  -- Cause: rewriting the RHS under `ofReal` congruence with a simp set
  -- cannot fire here; moreover the remaining goal after identifying the
  -- self-strategy value is exactly the Open reflected-supremum identity,
  -- so the honest close is that bridge, not an unfold of barrierSupValue
  -- (whose body cannot mention W).
  have hself : dividendValue X q 0 (barrierStrategy X 0 0) =
      barrierSupValue X 0 q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
  rw [hself]
  exact AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
    X hX q hq W hW
