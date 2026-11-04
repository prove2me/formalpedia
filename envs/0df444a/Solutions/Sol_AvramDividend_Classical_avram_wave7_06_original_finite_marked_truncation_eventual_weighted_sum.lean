-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_finite_marked_truncation_eventual_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:15:55.821477+00:00
-- url     : https://prove2.me/submissions/e9ab6188-6ea7-487e-b072-989d0ecf6a88

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal

/-- Exact finite original marked-time truncations stabilise on each source path. -/
theorem solution
    (F : Finset ℝ≥0) (G : ℕ → Finset ℝ≥0) (H : ℝ≥0 → ℝ)
    (hSub : ∀ n, G n ⊆ F)
    (hEach : ∀ u ∈ F, ∀ᶠ n in Filter.atTop, u ∈ G n) :
    ∀ᶠ n in Filter.atTop,
      (∑ u ∈ G n, H u) = ∑ u ∈ F, H u := by
  classical
  have hFinite : ∀ S : Finset ℝ≥0,
      (∀ u ∈ S, ∀ᶠ n in Filter.atTop, u ∈ G n) →
      ∀ᶠ n in Filter.atTop, ∀ u ∈ S, u ∈ G n := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        exact Filter.Eventually.of_forall (by
          intro n u hu
          simp at hu)
    | @insert u S hu ih =>
        intro h
        have huEv : ∀ᶠ n in Filter.atTop, u ∈ G n :=
          h u (Finset.mem_insert_self u S)
        have hTail : ∀ᶠ n in Filter.atTop, ∀ v ∈ S, v ∈ G n :=
          ih (by
            intro v hv
            exact h v (Finset.mem_insert_of_mem hv))
        filter_upwards [huEv, hTail] with n hn hnS v hv
        rcases Finset.mem_insert.mp hv with hEq | hvS
        · simpa [hEq] using hn
        · exact hnS v hvS
  filter_upwards [hFinite F hEach] with n hn
  have hEq : G n = F :=
    Finset.Subset.antisymm (hSub n) (by
      intro u hu
      exact hn u hu)
  rw [hEq]
