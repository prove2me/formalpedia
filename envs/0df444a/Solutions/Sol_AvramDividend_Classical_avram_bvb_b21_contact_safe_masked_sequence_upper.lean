-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_contact_safe_masked_sequence_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:02:15.833526+00:00
-- url     : https://prove2.me/submissions/61cf626b-bd6f-4b97-b210-ef9794ee2535

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical Filter Set
open scoped Topology
noncomputable section

/-- Zero outside the cap preserves a one-sided contact upper bound. -/
theorem solution
    {α : Type*} [TopologicalSpace α]
    (s : Set α) (x : α) (f : α → ℝ)
    (hcont : ContinuousWithinAt f s x) (hnonneg : 0 ≤ f x)
    (seq : ℕ → α) (hseq : Tendsto seq atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (if seq n ∈ s then f (seq n) else 0) ≤ f x + ε := by
  have hx : f x < f x + ε := lt_add_of_pos_right _ hε
  have hwithin : ∀ᶠ y in 𝓝[s] x, f y < f x + ε :=
    hcont.eventually (Iio_mem_nhds hx)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ s → f y < f x + ε :=
    (eventually_nhdsWithin_iff).1 hwithin
  filter_upwards [hseq.eventually hnear] with n hn
  by_cases hs : seq n ∈ s
  · simp only [if_pos hs]
    exact (hn hs).le
  · simp only [if_neg hs]
    linarith
