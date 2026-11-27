-- Prove2me | solution 1 for CompanionTheory.Mirab.Dim.extFun_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:11.086376+00:00
-- url     : https://prove2.me/submissions/4c67c397-4f87-4c3a-82f1-62fe4c0a3ff6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim
import Theorems.Thm_CompanionTheory_Mirab_Dim_cls_mul
import Theorems.Thm_CompanionTheory_Mirab_Dim_psiExt_mul
import Theorems.Thm_GlobalTheory_FiniteGL_mem_mirabInducedSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
variable (ψ₀ : AddChar k ℂ)
namespace CompanionTheory.Mirab.Dim
theorem _root_.solution (g : Cos k n → ℂ) : extFun n ψ₀ g ∈ MirabInducedSpace n ψ₀ := by
  rw [mem_mirabInducedSpace]
  intro u x
  unfold extFun
  have hr : rep n ((u : mirabSub k n) * x) = rep n x := by unfold rep; rw [cls_mul]
  rw [hr, cls_mul, mul_assoc, psiExt_mul n ψ₀ u _ (rep_mem n x), mul_assoc]
end CompanionTheory.Mirab.Dim
