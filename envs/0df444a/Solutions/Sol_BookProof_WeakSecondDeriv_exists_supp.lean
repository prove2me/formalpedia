-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.exists_supp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:48.697538+00:00
-- url     : https://prove2.me/submissions/03c2ec4c-adb2-4a19-b9b2-29db36618842

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.exists_supp
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) :
    ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Icc (-R) R := by

  obtain ⟨R, hR⟩ := (h.hasCompactSupport.isCompact.isBounded).subset_closedBall (0 : ℝ)
  refine ⟨|R|, abs_nonneg R, fun x hx => ?_⟩
  have hx' := hR hx
  rw [Real.closedBall_eq_Icc] at hx'
  simp only [zero_sub, zero_add, mem_Icc] at hx' ⊢
  exact ⟨by linarith [le_abs_self R, hx'.1], by linarith [le_abs_self R, hx'.2]⟩
