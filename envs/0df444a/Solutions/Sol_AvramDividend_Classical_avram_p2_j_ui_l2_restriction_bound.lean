-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_l2_restriction_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:29:21.422911+00:00
-- url     : https://prove2.me/submissions/52dc3f67-7f36-43e2-b8a0-4679ff36cd56

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-! Cauchy-Schwarz on a measurable restriction, uniformly in the source variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (B : ℝ≥0)
    (hm : AEStronglyMeasurable Y P)
    (hB : eLpNorm Y 2 P ≤ (B : ENNReal))
    (s : Set Ω) :
    eLpNorm Y 1 (P.restrict s) ≤
      (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by
  have h2 : MemLp Y 2 P :=
    ⟨hm, lt_of_le_of_lt hB (by simp)⟩
  have h2s : MemLp Y 2 (P.restrict s) := h2.restrict s
  have hcs :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := P.restrict s) (p := 1) (q := 2)
      (by norm_num) h2s.aestronglyMeasurable
  have hnorm : eLpNorm Y 2 (P.restrict s) ≤ (B : ENNReal) :=
    (eLpNorm_mono_measure Y (Measure.restrict_le_self)).trans hB
  have hcs' : eLpNorm Y 1 (P.restrict s) ≤
      eLpNorm Y 2 (P.restrict s) * (P s) ^ (1 / 2 : ℝ) := by
    convert hcs using 1 <;> norm_num
  exact hcs'.trans (by gcongr <;> exact hnorm)
