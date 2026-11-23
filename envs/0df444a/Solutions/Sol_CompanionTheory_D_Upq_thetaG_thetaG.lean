-- Prove2me | solution 1 for CompanionTheory.D.Upq.thetaG_thetaG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:41.088078+00:00
-- url     : https://prove2.me/submissions/6535f609-25e2-4ad3-870d-02b8a257dd0e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_mul_J_J

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
variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh
namespace CompanionTheory.D.Upq
theorem _root_.solution (M : Matrix n n ℂ) : thetaG J (thetaG J M) = M := by
  simp only [thetaG, conjTranspose_neg, conjTranspose_mul, hJh, conjTranspose_conjTranspose,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul, mul_J_J hJ]
end CompanionTheory.D.Upq
