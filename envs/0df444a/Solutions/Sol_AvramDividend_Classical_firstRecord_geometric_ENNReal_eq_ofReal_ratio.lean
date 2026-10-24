-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_geometric_ENNReal_eq_ofReal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:44:46.819008+00:00
-- url     : https://prove2.me/submissions/871c4e47-e6e3-4178-a2cd-8aa7694cec55

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-! Recover the real finite geometric quotient from the extended-nonnegative formula. -/
theorem solution
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 ≤ p) (hplt : p < 1) :
    ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) =
      ENNReal.ofReal (ε * p / (1 - p)) := by
  have hden : 0 < 1 - p := sub_pos.mpr hplt
  have hsub : ENNReal.ofReal (1 - p) = 1 - ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_sub (1 : ℝ) hp
  calc
    ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) =
        ENNReal.ofReal ε * (ENNReal.ofReal p * ENNReal.ofReal ((1 - p)⁻¹)) := by
          rw [← hsub, ← ENNReal.ofReal_inv_of_pos hden]
    _ = ENNReal.ofReal (ε * p / (1 - p)) := by
          rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hε]
          congr 1
          simp only [div_eq_mul_inv]
          ring
