-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_monotone_grid_step_zero_outside_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:41:00.25938+00:00
-- url     : https://prove2.me/submissions/7e86b939-1779-472a-8d7f-b728bcba0d73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- Every frozen grid-cell contribution vanishes outside its full row. -/
theorem solution
    (n : ℕ) (u : ℕ → ℝ) (hu : StrictMono u)
    (c : ℕ → ℝ) (t : ℝ)
    (ht : t ∉ Set.Ico (u 0) (u (n + 1))) :
    (∑ j ∈ Finset.range (n + 1),
      (Set.Ico (u j) (u (j + 1))).indicator (fun _ => c j) t) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j < n + 1 := Finset.mem_range.mp hj
  have hsub : Ico (u j) (u (j + 1)) ⊆ Ico (u 0) (u (n + 1)) := by
    intro r hr
    exact ⟨(hu.monotone (Nat.zero_le j)).trans hr.1,
      hr.2.trans_le (hu.monotone (Nat.succ_le_of_lt hj'))⟩
  have hnot : t ∉ Ico (u j) (u (j + 1)) := by
    intro hmem
    exact ht (hsub hmem)
  simp [Set.indicator, hnot]
