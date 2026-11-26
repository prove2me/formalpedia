-- Prove2me | solution 1 for FD1D.uniform_map_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:42:05.401542+00:00
-- url     : https://prove2.me/submissions/0e5523ce-2c19-4149-9746-95a21f7a7173

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_inventoryStatePerm_count
import Theorems.Thm_FD1D_inventoryStatePerm_image_count
import Theorems.Thm_FD1D_assignmentCount_perm
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.inventoryStatePerm_count
attribute [local simp] FD1D.inventoryStatePerm_image_count
attribute [local simp] FD1D.assignmentCount_perm

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [DecidableEq B]
    (f : A → B) (ea : Equiv.Perm A) (eb : Equiv.Perm B)
    (h : ∀ a, f (ea a) = eb (f a)) :
    FiniteKernel.LawInvariant
      ((FiniteLaw.uniform : FiniteLaw A).map f) eb := by
  intro b
  simp only [FiniteLaw.mass_map, FiniteLaw.mass_uniform]
  simp_rw [Finset.sum_filter]
  rw [← Equiv.sum_comp ea
    (fun a => if f a = eb b then
      (1 / Fintype.card A : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  rw [h]
  simp
end FD1D
