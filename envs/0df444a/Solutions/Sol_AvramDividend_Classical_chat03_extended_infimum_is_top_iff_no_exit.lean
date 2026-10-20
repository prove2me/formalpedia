-- Prove2me | solution 1 for AvramDividend.Classical.chat03_extended_infimum_is_top_iff_no_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:54:39.255782+00:00
-- url     : https://prove2.me/submissions/df43bc3b-8cec-4832-aa5a-9b87503d8dd8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-!
The official extended first-passage infimum is infinity exactly when
there is no witnessed strict crossing. Never interpret toNNReal infinity
as a genuine finite passage time.
-/
theorem solution
    (p : ℝ≥0 → Prop) :
    (⨅ (t : ℝ≥0) (_ : p t), (t : ℝ≥0∞)) = ∞ ↔
      ¬ ∃ t : ℝ≥0, p t := by
  constructor
  · intro htop
    rintro ⟨t, ht⟩
    have hle :
        (⨅ (s : ℝ≥0) (_ : p s), (s : ℝ≥0∞)) ≤ (t : ℝ≥0∞) :=
      iInf_le_of_le t (iInf_le _ ht)
    rw [htop] at hle
    exact (not_le_of_gt (ENNReal.coe_lt_top)) hle
  · intro hnone
    have hp : ∀ t : ℝ≥0, ¬ p t := by
      intro t ht
      exact hnone ⟨t, ht⟩
    simp [hp]