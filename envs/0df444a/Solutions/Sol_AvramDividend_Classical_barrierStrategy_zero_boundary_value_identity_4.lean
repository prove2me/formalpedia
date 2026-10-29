-- Prove2me | solution 4 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:01:32.933663+00:00
-- url     : https://prove2.me/submissions/d5663fb4-e5e2-4573-87c8-bc82a3127e41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
  -- Zero-boundary identity: value at 0 is the supremum value (Proved
  -- 11b589b7 barrierValue_self_eq_barrierSupValue), and the zero supremum
  -- value is the barrier function value (Open b83a725b
  -- zero_reflectedSupValue_eq_barrierValue).
  -- Next decomposition (not assumed here): unbounded side via Proved
  -- c1b8958a (W 0 = 0 from ¬BV) + 93b9d0c0 + ec1ef190/87b35c09 (need hNear or
  -- hRuin premise); BV side via Open 2bb529c8 stopped balance. Until those
  -- premises are established this remains a sketch, not a Proved dependency.
  rw [AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0,
    AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
      X hX q hq W hW]
