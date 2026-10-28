-- Prove2me | solution 2 for AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_upward_regularity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:01:05.869543+00:00
-- url     : https://prove2.me/submissions/62586e04-8b2f-4bc0-be42-3f636c04923b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W a) := by
  rw [AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
    X q a ha hplus, one_mul]
