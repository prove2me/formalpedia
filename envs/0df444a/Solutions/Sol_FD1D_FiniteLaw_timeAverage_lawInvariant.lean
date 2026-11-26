-- Prove2me | solution 1 for FD1D.FiniteLaw.timeAverage_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:55.324422+00:00
-- url     : https://prove2.me/submissions/7f363616-089b-4353-a8ac-4a7d6b97c647

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
import Theorems.Thm_FD1D_FiniteLaw_timeAverage_mass
import Theorems.Thm_FD1D_FiniteLaw_timeLiftPerm_apply
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.FiniteLaw.timeAverage_mass
attribute [local simp] FD1D.FiniteLaw.timeLiftPerm_apply

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (e : Equiv.Perm α)
    (hinv : ∀ t, FiniteKernel.LawInvariant (μ t) e) :
    FiniteKernel.LawInvariant (timeAverage hT μ) (timeLiftPerm e) := by
  intro z
  rcases z with ⟨t, x⟩
  simp only [timeLiftPerm_apply, timeAverage_mass]
  rw [hinv t x]
end FD1D.FiniteLaw
