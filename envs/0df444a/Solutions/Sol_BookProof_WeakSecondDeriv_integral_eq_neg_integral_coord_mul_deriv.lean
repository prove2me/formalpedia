-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:02.689363+00:00
-- url     : https://prove2.me/submissions/f2b280e7-0693-47fd-9077-f480d346d4a5

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_differentiable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_deriv
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_integrable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_coord_mul
import Theorems.Thm_BookProof_WeakSecondDeriv_integral_deriv_of_test
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) :
    ∫ x, g x = -∫ x, x * deriv g x := by

  have hd : deriv (fun x => x * g x) = fun x => g x + x * deriv g x := by
    funext x
    have h1 : HasDerivAt (fun x : ℝ => x * g x) (1 * g x + x * deriv g x) x :=
      (hasDerivAt_id x).mul (h.differentiable x).hasDerivAt
    rw [h1.deriv]; ring
  have h0 := integral_deriv_of_test h.coord_mul
  rw [hd] at h0
  rw [integral_add h.integrable h.deriv.coord_mul.integrable] at h0
  linarith
