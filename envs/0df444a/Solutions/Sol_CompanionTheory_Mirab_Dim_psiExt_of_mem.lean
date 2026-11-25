-- Prove2me | solution 1 for CompanionTheory.Mirab.Dim.psiExt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:05.050515+00:00
-- url     : https://prove2.me/submissions/3288c7c8-04f9-43a0-8b73-0ebd2ae70803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim

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
theorem _root_.solution (u : uniSub k n) : psiExt n ψ₀ (u : mirabSub k n) = genericChar n ψ₀ u := by
  unfold psiExt
  rw [dif_pos u.2]
end CompanionTheory.Mirab.Dim
