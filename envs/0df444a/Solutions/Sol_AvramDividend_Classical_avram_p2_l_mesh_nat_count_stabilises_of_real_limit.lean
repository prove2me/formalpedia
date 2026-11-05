-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_nat_count_stabilises_of_real_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:58:38.402525+00:00
-- url     : https://prove2.me/submissions/b0e519af-4e18-435f-b0b4-d16785d4273b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set

/-- A real-valued limit of genuine natural-number counts gives eventual
exact equality with the limiting count. -/
theorem solution (counts : ℕ → ℕ) (m : ℕ)
    (h : Tendsto (fun n : ℕ => (counts n : ℝ)) atTop (𝓝 (m : ℝ))) :
    ∀ᶠ n in atTop, counts n = m := by
  have hsmall : Ioo ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) ∈
      𝓝 (m : ℝ) := by
    apply isOpen_Ioo.mem_nhds
    constructor <;> norm_num
  have hev : ∀ᶠ n in atTop,
      (counts n : ℝ) ∈ Ioo ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) :=
    h.eventually hsmall
  filter_upwards [hev] with n hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnat : counts n + 1 ≤ m := Nat.succ_le_iff.mpr hlt
    have hreal : (counts n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast hnat
    exact (not_lt_of_ge hreal) (by linarith [hn.1])
  · have hnat : m + 1 ≤ counts n := Nat.succ_le_iff.mpr hgt
    have hreal : (m : ℝ) + 1 ≤ (counts n : ℝ) := by
      exact_mod_cast hnat
    exact (not_lt_of_ge hreal) (by linarith [hn.2])
