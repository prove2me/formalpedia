-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:41:15.064263+00:00
-- url     : https://prove2.me/submissions/69768181-1e1a-445d-aacf-d05e72923309

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_positive_ruin_excludes_terminal_atom
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (σ : ℝ≥0∞) (t : ℝ≥0)
    (ht : 0 < t) (hruin : (t : ℝ≥0∞) = σ) :
    paymentTimes σ ∩ Iic (t : ℝ) =
      paymentTimes σ ∩ Iio (t : ℝ) := by
  have hnone := (avram_p4_e_localise_positive_ruin_excludes_terminal_atom
    σ t ht hruin).2
  ext s
  constructor
  · intro hs
    refine ⟨hs.1, ?_⟩
    have hle : s ≤ (t : ℝ) := hs.2
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hsEq : s = (t : ℝ) := heq
      subst s
      exact hnone ⟨hs.1, hs.2⟩
  · intro hs
    have hlt : s < (t : ℝ) := hs.2
    exact ⟨hs.1, le_of_lt hlt⟩
