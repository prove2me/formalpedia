-- Prove2me | solution 1 for CompanionTheory.D.Upq.thetaG_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:13.612879+00:00
-- url     : https://prove2.me/submissions/26e4f76b-f326-408f-b055-a68bba98becd

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (J : Matrix n n ℂ)
variable {J}
namespace CompanionTheory.D.Upq
theorem _root_.solution (M N : Matrix n n ℂ) : thetaG J (M - N) = thetaG J M - thetaG J N := by
  simp only [thetaG, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, neg_sub_neg, neg_sub]
end CompanionTheory.D.Upq
