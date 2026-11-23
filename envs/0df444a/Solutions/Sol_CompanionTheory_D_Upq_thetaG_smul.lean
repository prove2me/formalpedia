-- Prove2me | solution 1 for CompanionTheory.D.Upq.thetaG_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:59.790788+00:00
-- url     : https://prove2.me/submissions/a770efea-54e6-439d-8f5a-19b104541190

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
theorem _root_.solution (c : ℂ) (M : Matrix n n ℂ) : thetaG J (c • M) = star c • thetaG J M := by
  simp only [thetaG, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
end CompanionTheory.D.Upq
