-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.deltaU_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:54.371897+00:00
-- url     : https://prove2.me/submissions/cb2f1b7e-4d81-4d6d-8646-e5e22e3e75d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr

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
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace CompanionTheory.Mirab.Irr
theorem _root_.solution (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ 1 = 1 := by
  unfold deltaU
  rw [dif_pos (one_mem _)]
  exact map_one (genericChar n ψ₀)
end CompanionTheory.Mirab.Irr
