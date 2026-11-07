-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:51:00.904417+00:00
-- url     : https://prove2.me/submissions/e70e634f-d448-4e79-870c-108949224678

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- Every fixed strict interior reserve eventually lies in the full
finite-cap predictable pre-reserve band [a_n,b_n]. -/
theorem solution (c d y : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hy : 0 < y) (hyc : y < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc (d / ((n : ℝ) + 1))
        (c * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
  have hyhalf : 0 < y / 2 := by linarith
  have hyhalfc : y / 2 < c := by linarith
  obtain ⟨Nlo, hNlo⟩ :=
    avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve
      c d (y / 2) hc hd hyhalf hyhalfc
  obtain ⟨Nhi, hNhi⟩ :=
    avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve
      c d y hc hd hy hyc
  refine ⟨max Nlo Nhi, ?_⟩
  intro n hn
  have hnlo : Nlo ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnhi : Nhi ≤ n := le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hlo, _⟩ := hNlo n hnlo
  obtain ⟨_, hhi⟩ := hNhi n hnhi
  change d / ((n : ℝ) + 1) ≤ y ∧
    y ≤ c * ((n : ℝ) + 1) / ((n : ℝ) + 2)
  constructor
  · have hlower : (d / ((n : ℝ) + 1)) / 2 ≤ y / 2 := hlo
    linarith
  · exact hhi
