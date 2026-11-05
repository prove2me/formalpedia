-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_ordered_mark_avoiding_perturbations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:39:32.745005+00:00
-- url     : https://prove2.me/submissions/9b6bf1f1-806a-4785-8ad1-2f90b994e3d6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_mark_joint_avoiding_cuts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Perturbed finite-mesh cuts avoid the selected marks and retain order. -/
theorem solution {ι : Type*} [Preorder ι] (S : Finset ℝ) (x : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : ι, i < j → x i + δ ≤ x j - δ) :
    ∃ y : ι → ℝ,
      (∀ i : ι, |y i - x i| < δ ∧ y i ∉ S) ∧ StrictMono y := by
  have hwindows : ∀ i : ι, x i - δ < x i + δ := by
    intro i
    linarith
  obtain ⟨y, hy⟩ := avram_p2_l_mesh_finite_mark_joint_avoiding_cuts
    S (fun i => x i - δ) (fun i => x i + δ) hwindows
  refine ⟨y, ?_, ?_⟩
  · intro i
    obtain ⟨hl, hr, hnot⟩ := hy i
    constructor
    · rw [abs_lt]
      constructor <;> linarith
    · exact hnot
  · intro i j hij
    have hi := (hy i).2.1
    have hj := (hy j).1
    have hgap := hsep i j hij
    linarith
