-- Prove2me | solution 1 for CompanionTheory.Mirab.Dim.restr_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:57:34.447914+00:00
-- url     : https://prove2.me/submissions/0c780460-8974-4e06-ae72-140884c8f535

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim
import Theorems.Thm_CompanionTheory_Mirab_Dim_cls_out
import Theorems.Thm_CompanionTheory_Mirab_Dim_psiExt_one
import Theorems.Thm_CompanionTheory_Mirab_Dim_extFun_mem

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
theorem _root_.solution : Function.Surjective (restr n ψ₀) := by
  intro g
  refine ⟨⟨extFun n ψ₀ g, extFun_mem n ψ₀ g⟩, ?_⟩
  funext c
  show extFun n ψ₀ g c.out = g c
  unfold extFun
  have hr : rep n c.out = c.out := by unfold rep; rw [cls_out]
  rw [hr, cls_out, mul_inv_cancel, psiExt_one, one_mul]
end CompanionTheory.Mirab.Dim
