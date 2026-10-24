-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_min_mono_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:00:22.72616+00:00
-- url     : https://prove2.me/submissions/5722f8c7-bd28-4dc7-aff7-2c23f8e1a06d

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expanding the truncation horizon never removes admissible payment times,
    including the initial atom of the dividend measure. -/
theorem solution (σ s t : ℝ≥0∞) (hst : s ≤ t) :
    paymentTimes (min σ s) ⊆ paymentTimes (min σ t) := by
  intro u hu
  rcases hu.2 with hzero | hpre
  · exact ⟨hu.1, Or.inl hzero⟩
  · have hσ : ENNReal.ofReal u < σ :=
      lt_of_lt_of_le hpre (min_le_left _ _)
    have hs : ENNReal.ofReal u < s :=
      lt_of_lt_of_le hpre (min_le_right _ _)
    exact ⟨hu.1, Or.inr (lt_min hσ (lt_of_lt_of_le hs hst))⟩
