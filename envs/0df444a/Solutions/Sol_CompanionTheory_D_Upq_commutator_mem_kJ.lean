-- Prove2me | solution 1 for CompanionTheory.D.Upq.commutator_mem_kJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:43.111775+00:00
-- url     : https://prove2.me/submissions/1798c3c0-34a6-4d25-808f-0a6fa82c8d70

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
variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
namespace CompanionTheory.D.Upq
theorem _root_.solution {X Y : Matrix n n ℂ} (hX : X ∈ kJ J) (hY : Y ∈ kJ J) :
    X * Y - Y * X ∈ kJ J :=
  ⟨commutator_mem_lieJ hX.1 hY.1, by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc X Y J, hY.2, ← Matrix.mul_assoc X J Y, hX.2,
      Matrix.mul_assoc Y X J, hX.2, ← Matrix.mul_assoc Y J X, hY.2, Matrix.mul_assoc J X Y,
      Matrix.mul_assoc J Y X]⟩
end CompanionTheory.D.Upq
