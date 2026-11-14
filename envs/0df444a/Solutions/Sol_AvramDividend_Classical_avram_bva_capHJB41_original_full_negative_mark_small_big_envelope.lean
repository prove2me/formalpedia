-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:51:49.893561+00:00
-- url     : https://prove2.me/submissions/4fc245a9-070c-48bf-9e4a-a0a70be11390

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

/- Revalidated HJB41 against current Prove2Me checker after old candidate admission became stale. -/
theorem solution
    (w : ℝ → ℝ) (c ε L M : ℝ)
    (hε : 0 < ε) (hεc : ε ≤ c)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hBound : ∀ r ∈ Icc (0 : ℝ) c, |w r| ≤ M)
    (hLip : ∀ a ∈ Icc (ε / 2) c, ∀ b ∈ Icc (ε / 2) c,
      |w a - w b| ≤ L * |a - b|)
    (y z : ℝ) (hy : y ∈ Icc ε c) (hz : z < 0) :
    ‖w (y + z) - w y‖ ≤
      ‖if -(ε / 2) ≤ z then L * |z| else 2 * M‖ := by
  have hy0 : 0 ≤ y := le_trans (le_of_lt hε) hy.1
  have hyB : |w y| ≤ M :=
    hBound y ⟨hy0, hy.2⟩
  by_cases hs : -(ε / 2) ≤ z
  · have hb : y + z ∈ Icc (ε / 2) c := by
      constructor
      · linarith [hy.1]
      · linarith [hy.2, hz]
    have ha : y ∈ Icc (ε / 2) c := by
      constructor
      · linarith [hy.1, hε]
      · exact hy.2
    have hLip' := hLip (y + z) hb y ha
    have hDiff : |y + z - y| = |z| := by
      ring
    rw [hDiff] at hLip'
    have hRight : 0 ≤ L * |z| := mul_nonneg hL (abs_nonneg z)
    simpa [Real.norm_eq_abs, hs, abs_of_nonneg hRight] using hLip'
  · have hyz : y + z ≤ c := by linarith [hy.2, hz]
    have hShiftBound : |w (y + z)| ≤ M := by
      by_cases hn : y + z < 0
      · rw [hwNeg (y + z) hn, abs_zero]
        exact hM
      · exact hBound (y + z) ⟨le_of_not_gt hn, hyz⟩
    have ht : |w (y + z) - w y| ≤ |w (y + z)| + |w y| := by
      simpa using (abs_sub_le (w (y + z)) 0 (w y))
    have htotal : |w (y + z) - w y| ≤ 2 * M := by linarith
    simpa only [Real.norm_eq_abs, if_neg hs, abs_of_nonneg (by positivity : 0 ≤ 2 * M)] using htotal
