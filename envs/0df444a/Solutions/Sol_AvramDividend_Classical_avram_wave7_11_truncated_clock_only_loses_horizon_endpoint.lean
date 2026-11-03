-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_truncated_clock_only_loses_horizon_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:26.150445+00:00
-- url     : https://prove2.me/submissions/555b0105-63a3-4db9-a21d-c00b89a4fcd7

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Truncating the source payment clock at a finite real horizon can lose
    only the exact horizon endpoint, never an earlier dividend time. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes σ ∩ Iic T ⊆
      (paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T) ∪ {T} := by
  intro t ht
  have hle : t ≤ T := ht.2
  rcases eq_or_lt_of_le hle with heq | hlt
  · right
    simpa [heq]
  · left
    have ht0 : 0 ≤ t := ht.1.1
    have htσ : t = 0 ∨ ENNReal.ofReal t < σ := ht.1.2
    have htT : ENNReal.ofReal t < ENNReal.ofReal T :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr hlt
    refine ⟨?_, ht.2⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (ENNReal.ofReal T))
    refine ⟨ht0, ?_⟩
    rcases htσ with hz | hs
    · exact Or.inl hz
    · exact Or.inr (lt_min hs htT)
