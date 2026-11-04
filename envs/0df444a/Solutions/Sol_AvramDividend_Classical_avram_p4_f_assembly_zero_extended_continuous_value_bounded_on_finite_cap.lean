-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:57:34.250863+00:00
-- url     : https://prove2.me/submissions/53c771a9-89ff-4d34-8d1d-fc93afb5c70b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- The original zero-extension and right-halfline continuity assumptions
    bound the verification value at every reserve below a finite cap. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, y ≤ c → |w y| ≤ B := by
  have hcont : ContinuousOn w (Icc 0 c) := by
    apply hw_cont.mono
    intro y hy
    exact hy.1
  have hK : IsCompact (w '' Icc 0 c) :=
    isCompact_Icc.image_of_continuousOn hcont
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro y hy
  by_cases hneg : y < 0
  · rw [hw_neg y hneg, abs_zero]
    exact le_max_right _ _
  · have hy0 : 0 ≤ y := le_of_not_gt hneg
    have hyI : y ∈ Icc (0 : ℝ) c := ⟨hy0, hy⟩
    have hmem : w y ∈ w '' Icc (0 : ℝ) c := ⟨y, hyI, rfl⟩
    have hb := hB (w y) hmem
    simpa only [Real.norm_eq_abs] using le_trans hb (le_max_left B 0)
