-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f18_discounted_finite_clock_split_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:16:04.343117+00:00
-- url     : https://prove2.me/submissions/1b8a767b-1cdc-4a84-8bdd-2e2316207ae7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (q : ℝ) (hq : 0 ≤ q) (ε : ℝ≥0) (t : ℝ≥0∞) :
    (if t < ⊤ then ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal t))) else 0) ≤
    (if t < (ε : ℝ≥0∞) then 1 else
      ENNReal.ofReal (Real.exp (-(q * (ε : ℝ))))) := by
  by_cases ht : t < (⊤ : ℝ≥0∞)
  · by_cases hε : t < (ε : ℝ≥0∞)
    · simp only [if_pos ht, if_pos hε]
      have hnonneg : 0 ≤ q * ENNReal.toReal t :=
        mul_nonneg hq ENNReal.toReal_nonneg
      have hreal : Real.exp (-(q * ENNReal.toReal t)) ≤ 1 :=
        (Real.exp_le_one_iff).2 (neg_nonpos.mpr hnonneg)
      simpa using (ENNReal.ofReal_le_ofReal hreal)
    · simp only [if_pos ht, if_neg hε]
      have hreal : (ε : ℝ) ≤ ENNReal.toReal t := by
        simpa using (ENNReal.toReal_mono (ne_of_lt ht) (le_of_not_gt hε))
      have hmul : q * (ε : ℝ) ≤ q * ENNReal.toReal t :=
        mul_le_mul_of_nonneg_left hreal hq
      exact ENNReal.ofReal_le_ofReal ((Real.exp_le_exp).2 (by linarith))
  · have htop : t = ⊤ := top_unique (le_of_not_gt ht)
    subst t
    simp
