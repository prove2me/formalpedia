-- Prove2me | solution 1 for CompanionTheory.D.Upq.mem_lieJ_iff_thetaG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:08.19059+00:00
-- url     : https://prove2.me/submissions/ef503a13-8268-42af-b721-7f1e843f6230

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_mul_J_J
import Theorems.Thm_CompanionTheory_D_Upq_mem_lieJ_iff

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
omit hJh
namespace CompanionTheory.D.Upq
theorem _root_.solution {X : Matrix n n ℂ} : X ∈ lieJ J ↔ thetaG J X = X := by
  rw [mem_lieJ_iff hJ, thetaG]
  constructor
  · intro h
    rw [h]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
      mul_J_J hJ]
  · intro h
    calc Xᴴ = J * (J * Xᴴ * J) * J := by
          simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul, mul_J_J hJ]
      _ = -(J * (-(J * Xᴴ * J)) * J) := by simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      _ = -(J * X * J) := by rw [h]
end CompanionTheory.D.Upq
