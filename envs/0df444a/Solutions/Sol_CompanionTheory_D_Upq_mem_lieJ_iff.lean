-- Prove2me | solution 1 for CompanionTheory.D.Upq.mem_lieJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:14.163544+00:00
-- url     : https://prove2.me/submissions/5bbb3081-a7b6-4e6a-8999-c17cf30f8bef

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
variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
namespace CompanionTheory.D.Upq
theorem _root_.solution {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ = -(J * X * J) := by
  constructor
  · intro h
    calc Xᴴ = Xᴴ * J * J := (mul_J_J hJ _).symm
      _ = -(J * X * J) := by rw [conjTranspose_mul_eq_of_mem h, Matrix.neg_mul]
  · intro h
    show Xᴴ * J + J * X = 0
    rw [h, Matrix.neg_mul, mul_J_J hJ, neg_add_cancel]
end CompanionTheory.D.Upq
