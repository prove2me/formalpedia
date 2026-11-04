-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_positive_ruin_excludes_terminal_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:01:28.0303+00:00
-- url     : https://prove2.me/submissions/af0c6d52-e951-4173-ab63-36cdc565155f

import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At positive ruin, zero remains in the source payment clock but ruin itself does not. -/
theorem solution
    (σ : ℝ≥0∞) (t : ℝ≥0)
    (ht : 0 < t) (hruin : (t : ℝ≥0∞) = σ) :
    (0 : ℝ) ∈ paymentTimes σ ∩ Iic (t : ℝ) ∧
    (t : ℝ) ∉ paymentTimes σ ∩ Iic (t : ℝ) := by
  constructor
  · constructor
    · simp [paymentTimes]
    · exact_mod_cast (show (0 : ℝ≥0) ≤ t from zero_le)
  · intro h
    have hp : (t : ℝ) ∈ paymentTimes σ := h.1
    change 0 ≤ (t : ℝ) ∧ ((t : ℝ) = 0 ∨ ENNReal.ofReal (t : ℝ) < σ) at hp
    rcases hp.2 with hz | hlt
    · have hpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      exact (ne_of_gt hpos) hz
    · have hco : ENNReal.ofReal (t : ℝ) = (t : ℝ≥0∞) := by simp
      rw [hco, hruin] at hlt
      exact (lt_irrefl σ) hlt
