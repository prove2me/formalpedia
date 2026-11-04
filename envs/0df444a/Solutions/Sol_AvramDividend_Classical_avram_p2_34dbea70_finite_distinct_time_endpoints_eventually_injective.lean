-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:46:05.437176+00:00
-- url     : https://prove2.me/submissions/7e17ca8a-30d5-4d0e-b7e3-6b1dea97c637

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- A finite family of labelled source times has eventually distinct
approximating endpoints whenever every endpoint converges to its label. -/
theorem solution
    (F : Finset ℝ≥0) (b : ℝ≥0 → ℕ → ℝ≥0)
    (hb : ∀ u ∈ F, Tendsto (b u) atTop (𝓝 u)) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun u : ℝ≥0 => b u n) (F : Set ℝ≥0) := by
  classical
  have hpairs : ∀ᶠ n : ℕ in atTop,
      ∀ u ∈ F, ∀ v ∈ F, u ≠ v → b u n ≠ b v n := by
    apply (Filter.eventually_all_finset F).2
    intro u hu
    apply (Filter.eventually_all_finset F).2
    intro v hv
    by_cases huv : u = v
    · exact Filter.Eventually.of_forall (fun _ hne => (hne huv).elim)
    · rcases lt_or_gt_of_ne huv with hlt | hgt
      · exact ((hb u hu).eventually_lt (hb v hv) hlt).mono
          (fun _ hlt' _ => ne_of_lt hlt')
      · exact ((hb v hv).eventually_lt (hb u hu) hgt).mono
          (fun _ hgt' _ => ne_of_gt hgt')
  filter_upwards [hpairs] with n hn
  intro u hu v hv heq
  by_contra hne
  exact (hn u hu v hv hne) heq
