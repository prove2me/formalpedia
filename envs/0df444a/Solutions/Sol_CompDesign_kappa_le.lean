-- Prove2me | solution 1 for CompDesign.kappa_le
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:26:17.589748+00:00
-- url     : https://prove2.me/submissions/a4259a03-935f-4f66-a51e-3046e157c206

import Mathlib
import Definitions.Def_CompDesign_kappa

theorem solution (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) : CompDesign.kappa l ≤ 1 / (1 - l) := by
  have hpos : 0 < 1 - l := by linarith
  apply csSup_le
  · exact ⟨0, 0, Fin.elim0, fun j => j.elim0, by simp, by simp⟩
  · rintro s ⟨m, x, hx, hsum, rfl⟩
    have hterm : ∀ j, x j / (1 - x j) ≤ x j / (1 - l) := by
      intro j
      have h1 : 0 < 1 - x j := by linarith [(hx j).2]
      exact div_le_div_of_nonneg_left (hx j).1 hpos (by linarith [(hx j).2])
    calc ∑ j, x j / (1 - x j) ≤ ∑ j, x j / (1 - l) := Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j, x j) / (1 - l) := by rw [Finset.sum_div]
      _ ≤ 1 / (1 - l) := div_le_div_of_nonneg_right hsum hpos.le
