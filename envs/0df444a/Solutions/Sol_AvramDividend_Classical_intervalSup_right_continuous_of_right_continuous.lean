-- Prove2me | solution 1 for AvramDividend.Classical.intervalSup_right_continuous_of_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:13:23.529985+00:00
-- url     : https://prove2.me/submissions/2ecaeb4b-05e9-4898-86b6-9b0bbc591069

import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-- Supremum over growing compact time intervals preserves path right-continuity. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hB : ∀ t : ℝ≥0, BddAbove (f '' Set.Icc 0 t))
    (hf : ∀ t : ℝ≥0, Tendsto f (𝓝[≥] t) (𝓝 (f t))) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => sSup (f '' Set.Icc 0 s)) (Set.Ici t) t := by
  let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
  have hne (t : ℝ≥0) : (f '' Set.Icc 0 t).Nonempty := by
    refine ⟨f 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hmono : Monotone M := by
    intro s t hst
    apply csSup_le (hne s)
    rintro y ⟨r, hr, rfl⟩
    apply le_csSup (hB t)
    exact ⟨r, ⟨hr.1, hr.2.trans hst⟩, rfl⟩
  have hdom : ∀ t : ℝ≥0, f t ≤ M t := by
    intro t
    apply le_csSup (hB t)
    exact ⟨t, by simp, rfl⟩
  have hrepr : ∀ t : ℝ≥0, M t =
      ⨆ r : Set.Icc (0 : ℝ≥0) t, f r.1 := by
    intro t
    change sSup (f '' Set.Icc 0 t) =
      ⨆ r : Set.Icc (0 : ℝ≥0) t, f r.1
    exact sSup_image'
  intro t
  exact AvramDividend.Classical.runningSup_right_continuous_of_right_continuous
    f M hmono hdom hrepr hf t
