-- Prove2me | solution 1 for CompanionTheory.Mirab.Dim.psiExt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:48.83642+00:00
-- url     : https://prove2.me/submissions/c059da77-42b8-4f30-b16e-dbbb22e4fab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim
import Theorems.Thm_CompanionTheory_Mirab_Dim_psiExt_of_mem

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
theorem _root_.solution : psiExt n ψ₀ 1 = 1 := by
  have h := psiExt_of_mem n ψ₀ 1
  rw [OneMemClass.coe_one, map_one] at h
  exact h
end CompanionTheory.Mirab.Dim
