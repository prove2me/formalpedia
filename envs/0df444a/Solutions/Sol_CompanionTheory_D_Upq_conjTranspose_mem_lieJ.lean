-- Prove2me | solution 1 for CompanionTheory.D.Upq.conjTranspose_mem_lieJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.642831+00:00
-- url     : https://prove2.me/submissions/7682b171-5534-412e-a330-819a900f4739

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
variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
namespace CompanionTheory.D.Upq
theorem _root_.solution {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ ∈ lieJ J := by
  rw [mem_lieJ_iff hJ] at hX ⊢
  rw [conjTranspose_conjTranspose, hX]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
    mul_J_J hJ]
end CompanionTheory.D.Upq
