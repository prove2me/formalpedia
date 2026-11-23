-- Prove2me | solution 1 for CompanionTheory.D.Upq.thetaG_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:41.218964+00:00
-- url     : https://prove2.me/submissions/208abe13-f492-4857-a904-f77f32b1bbd6

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
theorem _root_.solution (M N : Matrix n n ℂ) : thetaG J (M + N) = thetaG J M + thetaG J N := by
  simp only [thetaG, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
end CompanionTheory.D.Upq
