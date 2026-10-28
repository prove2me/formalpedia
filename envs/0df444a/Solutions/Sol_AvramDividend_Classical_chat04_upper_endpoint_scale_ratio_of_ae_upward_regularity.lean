-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_scale_ratio_of_ae_upward_regularity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:03:20.745826+00:00
-- url     : https://prove2.me/submissions/6f6fa27d-a0c8-4721-b11f-87358f0c72ae

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.Algebra.Order.Field.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) := by
  rw [AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
      X q a ha hplus,
    div_self (AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha).ne',
    ENNReal.ofReal_one]
