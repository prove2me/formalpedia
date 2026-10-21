-- Prove2me | solution 1 for AvramDividend.Classical.chat03_rightcontinuous_separated_strict_passages_no_finite_tie
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:09:19.286474+00:00
-- url     : https://prove2.me/submissions/93613e8a-9f54-44a8-8002-1198fb18470e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Bounds.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-!
For a right-continuous real path, the infima of strict passages
through two separated barriers cannot both be the same finite time.
-/
theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (lower upper : ℝ)
    (hsep : lower < upper)
    (hRight : ContinuousWithinAt f (Set.Ici t) t)
    (hUp : IsGLB {s : ℝ≥0 | upper < f s} t)
    (hDown : IsGLB {s : ℝ≥0 | f s < lower} t) :
    False := by
  by_cases ht : f t < upper
  · have hright : ∀ᶠ s in 𝓝[Set.Ici t] t, f s < upper :=
      hRight.eventually (isOpen_Iio.mem_nhds ht)
    have hnhds : ∀ᶠ s in 𝓝 t,
        s ∈ Set.Ici t → f s < upper :=
      eventually_nhdsWithin_iff.mp hright
    have hmem :
        {s : ℝ≥0 | s ∈ Set.Ici t → f s < upper} ∈ 𝓝 t := hnhds
    obtain ⟨u, hu, hsub⟩ :=
      exists_Ico_subset_of_mem_nhds' hmem
        (lt_add_of_pos_right t zero_lt_one)
    have hbound : u ∈ lowerBounds {s : ℝ≥0 | upper < f s} := by
      intro s hs
      by_contra hsu
      have hts : t ≤ s := hUp.1 hs
      have hst : s < u := lt_of_not_ge hsu
      exact (not_lt_of_ge (le_of_lt ((hsub ⟨hts, hst⟩) hts))) hs
    exact (not_le_of_gt hu.1) (hUp.2 hbound)
  · have ht' : lower < f t :=
      lt_of_lt_of_le hsep (le_of_not_gt ht)
    have hright : ∀ᶠ s in 𝓝[Set.Ici t] t, lower < f s :=
      hRight.eventually (isOpen_Ioi.mem_nhds ht')
    have hnhds : ∀ᶠ s in 𝓝 t,
        s ∈ Set.Ici t → lower < f s :=
      eventually_nhdsWithin_iff.mp hright
    have hmem :
        {s : ℝ≥0 | s ∈ Set.Ici t → lower < f s} ∈ 𝓝 t := hnhds
    obtain ⟨u, hu, hsub⟩ :=
      exists_Ico_subset_of_mem_nhds' hmem
        (lt_add_of_pos_right t zero_lt_one)
    have hbound : u ∈ lowerBounds {s : ℝ≥0 | f s < lower} := by
      intro s hs
      by_contra hsu
      have hts : t ≤ s := hDown.1 hs
      have hst : s < u := lt_of_not_ge hsu
      exact (not_lt_of_ge (le_of_lt ((hsub ⟨hts, hst⟩) hts))) hs
    exact (not_le_of_gt hu.1) (hDown.2 hbound)
