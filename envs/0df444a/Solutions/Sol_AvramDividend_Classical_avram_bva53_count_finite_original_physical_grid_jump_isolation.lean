-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva53_count_finite_original_physical_grid_jump_isolation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:41:05.416429+00:00
-- url     : https://prove2.me/submissions/177bb3fb-ae49-4543-bd24-ef5f88051ddb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva50_original_physical_u_grid_finite_jump_cell_isolation
import Theorems.Thm_AvramDividend_Classical_avram_bva51_finite_count_mark_times_real_finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite intrinsic counting mass isolates original jump times on the physical grid. -/
theorem solution (S : Set ℝ≥0) (hCount : (Measure.count S) < ⊤)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, ∀ s t : ℝ≥0,
      s ∈ S → t ∈ S → u n i ≤ s → s < u n (i + 1) →
      u n i ≤ t → t < u n (i + 1) → s = t := by
  obtain ⟨F, hF⟩ := avram_bva51_finite_count_mark_times_real_finset S hCount
  have hcell := avram_bva50_original_physical_u_grid_finite_jump_cell_isolation
    F T hT u huniform
  filter_upwards [hcell] with n hn
  intro i s t hs ht hsl hsr htl htr
  have hsF : (s : ℝ) ∈ F := (hF s).mp hs
  have htF : (t : ℝ) ∈ F := (hF t).mp ht
  have hsl' : (u n i : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsl
  have hsr' : (s : ℝ) < (u n (i + 1) : ℝ) := by exact_mod_cast hsr
  have htl' : (u n i : ℝ) ≤ (t : ℝ) := by exact_mod_cast htl
  have htr' : (t : ℝ) < (u n (i + 1) : ℝ) := by exact_mod_cast htr
  exact NNReal.coe_injective
    (hn i (s : ℝ) (t : ℝ) hsF htF hsl' hsr' htl' htr')
