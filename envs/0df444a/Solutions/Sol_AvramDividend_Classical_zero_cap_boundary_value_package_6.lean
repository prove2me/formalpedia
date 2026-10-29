-- Prove2me | solution 6 for AvramDividend.Classical.zero_cap_boundary_value_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:12:22.445721+00:00
-- url     : https://prove2.me/submissions/fedb47e8-f732-4f3e-9474-978e025acee7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  -- Conjunct 1 is Proved: nonnegativity of the zero-barrier candidate
  -- at the origin (eb66042a), same binders.
  -- Conjunct 2 is the Proved zero-cap reduction (d58a54f2) applied to the
  -- Open zero-boundary identity (c2921c8c): the reflected zero-barrier
  -- dividend value equals the scale-function boundary formula.
  -- At best SKETCH_ACCEPTED until c2921c8c is Proved.
  have hnn : 0 ≤ barrierValue W 0 0 :=
    AvramDividend.Classical.barrierValue_zero_zero_nonneg X hX q hq W hW
  have hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
      X hX q hq W hW
  exact ⟨hnn,
    AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_boundary
      X hX q hq W hboundary⟩
