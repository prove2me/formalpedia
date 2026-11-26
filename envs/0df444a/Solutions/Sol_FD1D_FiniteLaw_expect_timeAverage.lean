-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_timeAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:37.31742+00:00
-- url     : https://prove2.me/submissions/a92bae24-a9f6-4479-ae08-cee704b39bbc

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
import Theorems.Thm_FD1D_FiniteLaw_timeAverage_mass
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.FiniteLaw.timeAverage_mass

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (f : Fin T × α → ℝ) :
    (timeAverage hT μ).expect f =
      (∑ t : Fin T, (μ t).expect (fun x => f (t, x))) / (T : ℝ) := by
  rw [expect, Fintype.sum_prod_type]
  simp only [expect]
  calc
    (∑ t : Fin T, ∑ x : α,
        (1 / (T : ℝ)) * (μ t).mass x * f (t, x)) =
        (1 / (T : ℝ)) *
          ∑ t : Fin T, ∑ x : α, (μ t).mass x * f (t, x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = (∑ t : Fin T, ∑ x : α, (μ t).mass x * f (t, x)) /
          (T : ℝ) := by ring
end FD1D.FiniteLaw
