-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_finite_mark_nearby_cuts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:39:05.276135+00:00
-- url     : https://prove2.me/submissions/6bbdcaef-e01b-451a-9287-478b24886127

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_mark_joint_avoiding_cuts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Perturb the nominal finite-mesh cuts without landing on selected marks. -/
theorem solution {ι : Type*} (S : Finset ℝ) (x : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ y : ι → ℝ, ∀ i : ι, |y i - x i| < δ ∧ y i ∉ S := by
  have hwindows : ∀ i : ι, x i - δ < x i + δ := by
    intro i
    linarith
  obtain ⟨y, hy⟩ := avram_p2_l_mesh_finite_mark_joint_avoiding_cuts
    S (fun i => x i - δ) (fun i => x i + δ) hwindows
  refine ⟨y, ?_⟩
  intro i
  obtain ⟨hl, hr, hnot⟩ := hy i
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  · exact hnot
