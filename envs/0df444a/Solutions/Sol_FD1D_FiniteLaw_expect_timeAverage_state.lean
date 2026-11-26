-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_timeAverage_state
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:21.082774+00:00
-- url     : https://prove2.me/submissions/26b6e77d-0bcd-469e-a929-1bfc05dbb54c

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
import Theorems.Thm_FD1D_FiniteLaw_timeAverage_mass
import Theorems.Thm_FD1D_FiniteLaw_expect_timeAverage_eq_sum_range
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
    (μ : ℕ → FiniteLaw α) (f : α → ℝ) :
    (timeAverage hT (fun t : Fin T => μ t)).expect
        (fun z => f z.2) =
      (∑ t ∈ Finset.range T, (μ t).expect f) / (T : ℝ) := by
  simpa using expect_timeAverage_eq_sum_range hT μ (fun _ => f)
end FD1D.FiniteLaw
