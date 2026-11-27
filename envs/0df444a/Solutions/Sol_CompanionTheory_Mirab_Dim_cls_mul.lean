-- Prove2me | solution 1 for CompanionTheory.Mirab.Dim.cls_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:56.55681+00:00
-- url     : https://prove2.me/submissions/283f011a-54f8-41de-b3b9-0ea7ec1c9d55

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
namespace CompanionTheory.Mirab.Dim
theorem _root_.solution (u : uniSub k n) (x : mirabSub k n) : cls n ((u : mirabSub k n) * x) = cls n x := by
  unfold cls
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  rw [mul_inv_rev, mul_inv_cancel_left]
  exact inv_mem u.2
end CompanionTheory.Mirab.Dim
