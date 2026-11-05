-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:37:12.958005+00:00
-- url     : https://prove2.me/submissions/a075d4b4-ee41-427a-b893-1e5c4ce62045

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original P4-F continuity and finite-cap extension construct their own
exponential value envelope with no extra growth assumption. -/
theorem solution
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, ‖V z‖ ≤ K * Real.exp z := by
  obtain ⟨M, hM, hBound⟩ :=
    avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
      C w hw_cont
  refine ⟨M + 1, by linarith, ?_⟩
  exact avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
    C hC w V hw_neg hVfinite M hM hBound
