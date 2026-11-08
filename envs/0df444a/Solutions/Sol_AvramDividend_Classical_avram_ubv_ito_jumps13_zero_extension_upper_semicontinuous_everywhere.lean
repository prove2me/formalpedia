-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps13_zero_extension_upper_semicontinuous_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:46:34.730896+00:00
-- url     : https://prove2.me/submissions/819afb81-2ee5-4fcc-9fd2-fcac5610a890

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_zero_extension_upper_contact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-! The original reserve-value zero extension is upper semicontinuous at every point. -/
theorem solution
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∀ x ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, |y - x| < δ → w y ≤ w x + ε := by
  intro x ε hε
  by_cases hx0 : x = 0
  · subst x
    simpa using
      (avram_ubv_ito_jumps13_zero_extension_upper_contact
        w hw0 hwcont hwneg ε hε)
  by_cases hx : 0 < x
  · have hc : ContinuousWithinAt w (Ici (0 : ℝ)) x :=
      hwcont x (by exact le_of_lt hx)
    obtain ⟨η, hη, hnear⟩ :=
      (Metric.continuousWithinAt_iff.mp hc) ε hε
    refine ⟨min η x, lt_min hη hx, ?_⟩
    intro y hy
    have hdist : dist y x < η := by
      simpa [Real.dist_eq] using (lt_of_lt_of_le hy (min_le_left η x))
    have hnonneg : 0 ≤ y := by
      have hylo := (abs_lt.mp (lt_of_lt_of_le hy (min_le_right η x))).1
      linarith
    have hdiff : |w y - w x| < ε := by
      simpa [Real.dist_eq] using hnear (show y ∈ Ici (0 : ℝ) from hnonneg) hdist
    linarith [(abs_lt.mp hdiff).2]
  · have hxneg : x < 0 := by
      rcases lt_trichotomy x 0 with h | h | h
      · exact h
      · exact False.elim (hx0 h)
      · exact False.elim (hx h)
    refine ⟨-x, by linarith, ?_⟩
    intro y hy
    have hyneg : y < 0 := by
      have hyupper := (abs_lt.mp hy).2
      linarith
    rw [hwneg y hyneg, hwneg x hxneg]
    simpa using (le_of_lt hε)
