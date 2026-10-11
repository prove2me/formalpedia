-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.integral_deriv_of_test
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:00.668711+00:00
-- url     : https://prove2.me/submissions/3f6c2329-4c1a-43f7-9b41-f0abf7ba56ff

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.integral_deriv_of_test
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_continuous
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_differentiable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_deriv
import Theorems.Thm_BookProof_WeakSecondDeriv_exists_supp
import Theorems.Thm_BookProof_WeakSecondDeriv_eq_zero_out
import Theorems.Thm_BookProof_WeakSecondDeriv_deriv_eq_zero_out
import Theorems.Thm_BookProof_WeakSecondDeriv_integral_eq_intervalIntegral
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) : ∫ x, deriv g x = 0 := by

  obtain ⟨R, hR, hsupp⟩ := exists_supp h
  rw [integral_eq_intervalIntegral (R := R) (a := -R - 1) (b := R + 1) hR
    (fun x hx => deriv_eq_zero_out hsupp hx) (by linarith) (by linarith)]
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => h.differentiable x)
    (h.deriv.continuous.intervalIntegrable _ _)]
  rw [eq_zero_out hsupp (by simp), eq_zero_out (x := -R - 1) hsupp (by simp)]
  ring
