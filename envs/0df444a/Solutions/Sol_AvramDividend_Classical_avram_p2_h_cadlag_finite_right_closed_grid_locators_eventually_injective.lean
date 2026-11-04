-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:14:28.75422+00:00
-- url     : https://prove2.me/submissions/70d16757-aa0b-42a0-aa8c-c2fdbcff3ae3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Distinct finite jump times have eventually distinct right-closed
uniform-grid cell indices whenever their upper endpoints converge. -/
theorem solution
    (S : Finset ℝ≥0) (j : ℕ → ℝ≥0 → ℕ) (T : ℝ≥0)
    (hb : ∀ u ∈ S,
      Tendsto (fun n : ℕ =>
        (((j n u + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
        atTop (𝓝 u)) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (j n) (S : Set ℝ≥0) := by
  let b : ℝ≥0 → ℕ → ℝ≥0 :=
    fun u n => (((j n u + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
  have hlim : ∀ u ∈ S, Tendsto (b u) atTop (𝓝 u) := by
    intro u hu
    simpa only [b] using hb u hu
  have hsep :=
    avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective
      S b hlim
  filter_upwards [hsep] with n hindex
  intro u hu v hv heq
  apply hindex hu hv
  simpa only [b, heq]
