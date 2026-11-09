-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_single_step_rightLimit_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:16:11.296193+00:00
-- url     : https://prove2.me/submissions/54b26d63-2284-4d53-9a4f-2736ec0ba88d

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source rightLimit is the infimum of all future dividends; for a
nonnegative single clock step this is zero before the clock and K at/after it. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (K : Ω → ℝ)
    (hK : ∀ ω, 0 ≤ K ω)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω) :
    ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω := by
  intro ω t
  by_cases ht : t < s
  · haveI : Nonempty (Ioi t) := ⟨⟨s, ht⟩⟩
    have hnonneg (u : Ioi t) : 0 ≤ D u ω := by
      rw [hD]
      split_ifs
      · exact le_refl _
      · exact hK ω
    have hbdd : BddBelow (Set.range (fun u : Ioi t => D u ω)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨u, rfl⟩
      exact hnonneg u
    rw [if_pos ht]
    apply le_antisymm
    · have hle : rightLimit D t ω ≤ D s ω := by
        change (⨅ u : Ioi t, D u ω) ≤ D s ω
        exact ciInf_le hbdd ⟨s, ht⟩
      have hz : D s ω = 0 := by
        rw [hD]
        simp
      simpa [hz] using hle
    · change 0 ≤ ⨅ u : Ioi t, D u ω
      exact le_ciInf hnonneg
  · haveI : Nonempty (Ioi t) :=
      ⟨⟨t + 1, lt_add_of_pos_right t (by norm_num : (0 : ℝ≥0) < 1)⟩⟩
    rw [if_neg ht]
    have hfuture : ∀ u : Ioi t, D u ω = K ω := by
      intro u
      have hu : s < (u : ℝ≥0) :=
        lt_of_le_of_lt (le_of_not_gt ht) u.property
      rw [hD]
      simp [not_le.mpr hu]
    change (⨅ u : Ioi t, D u ω) = K ω
    simp_rw [hfuture]
    simp
