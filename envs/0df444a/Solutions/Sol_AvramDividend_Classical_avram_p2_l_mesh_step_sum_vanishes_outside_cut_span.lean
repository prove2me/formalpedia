-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_step_sum_vanishes_outside_cut_span
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:55:05.618794+00:00
-- url     : https://prove2.me/submissions/3118eb3b-d64b-4c20-9995-2e6f2ef97857

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped BigOperators

/-- Outside a monotone finite partition, no half-open step cell is active. -/
theorem solution {n : ℕ} (p : Fin (n + 1) → ℝ) (c : Fin n → ℝ)
    (hp : Monotone p) (z : ℝ)
    (hz : z ≤ p 0 ∨ p (Fin.last n) < z) :
    (∑ i : Fin n,
      if z ∈ Ioc (p i.castSucc) (p i.succ) then c i else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : z ∉ Ioc (p i.castSucc) (p i.succ) := by
    intro hcell
    rcases hz with hl | hr
    · have hfirst : p 0 ≤ p i.castSucc := hp (by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_zero, Fin.val_castSucc]
        omega)
      have hzle : z ≤ p i.castSucc := le_trans hl hfirst
      exact (not_lt_of_ge hzle) hcell.1
    · have hlast : p i.succ ≤ p (Fin.last n) := hp (by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_last]
        omega)
      have hzle : z ≤ p (Fin.last n) := le_trans hcell.2 hlast
      exact (not_le_of_gt hr) hzle
  exact if_neg hnot
