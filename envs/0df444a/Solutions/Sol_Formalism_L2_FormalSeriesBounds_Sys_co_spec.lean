-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.co_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:31.079916+00:00
-- url     : https://prove2.me/submissions/28ebd19b-a2b7-426b-b551-421397cf507b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_U_det_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
open Formalism.L2.FormalSeriesBounds.Sys
variable {X : Cart V d I J} (S : Sys X)
namespace Formalism.L2.FormalSeriesBounds.Sys
theorem _root_.solution (h : I ⊕ J → C) (k : I) : ∑ b, S.co h b * S.U b k = h (Sum.inl k) := by
  have hU : S.U⁻¹ * S.U = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : ∀ j, ∑ b, S.U⁻¹ j b * S.U b k = (1 : Matrix I I C) j k := fun j => by
    rw [← hU, Matrix.mul_apply]
  simp only [co, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, e, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
end Formalism.L2.FormalSeriesBounds.Sys
