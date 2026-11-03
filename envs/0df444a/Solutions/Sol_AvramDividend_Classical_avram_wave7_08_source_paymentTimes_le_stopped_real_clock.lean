-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_paymentTimes_le_stopped_real_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:26:30.573189+00:00
-- url     : https://prove2.me/submissions/ce2a0dc4-4d0e-470f-a8cc-a68863640e1c

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_n_paymentTimes_source_ruin_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    (σ : ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆
      paymentTimes σ ∩ Iic (((min σ (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ) := by
  intro t ht
  refine ⟨(avram_wave7_08_positive_n_paymentTimes_source_ruin_le σ n hn ht).1, ?_⟩
  change t ≤ (((min σ (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ)
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (n : ℝ≥0∞)) at ht
  rcases ht.2 with hzero | hlt
  · subst t
    positivity
  · have hfin : min σ (n : ℝ≥0∞) ≠ ⊤ := by
      have htop : min σ (n : ℝ≥0∞) < ⊤ :=
        lt_of_le_of_lt (min_le_right σ (n : ℝ≥0∞)) (by simp)
      exact ne_of_lt htop
    have hcast :
        (((min σ (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
          min σ (n : ℝ≥0∞) := ENNReal.coe_toNNReal hfin
    have hltco :
        ENNReal.ofReal t <
          (((min σ (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [hcast]
      exact hlt
    exact le_of_lt ((ENNReal.ofReal_lt_coe_iff ht.1).mp hltco)
