-- Prove2me | solution 1 for Formalism.L2.Indef.ColData.pairing_condition_of_inverse_matrix_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:43.988274+00:00
-- url     : https://prove2.me/submissions/5cd02a0c-b766-4c34-8fb2-156d6c33c423

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_vw_inv
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_B
import Theorems.Thm_P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_sE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Indef.ColData.invZ_B
attribute [local simp] Formalism.L2.Indef.ColData.invZ_ζ
attribute [local simp] Formalism.L2.Indef.ColData.invZ_sE

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)
namespace Formalism.L2.Indef.ColData
theorem _root_.solution (h : C.MatrixIdentityOffBase) : C.invZ.PairingFactorsThroughPeriods := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u t φ F => ?_, fun u => ?_, fun u t => ?_, fun u w => ?_⟩
  · simp only [invZ_ζ, invZ_B]
    rw [← h1 u t φ F, ← mul_assoc, inv_mul_cancel₀ (h3 u t), one_mul]
  · simp [h2 u]
  · simpa using h3 u t
  · simp only [invZ_ζ]
    rw [vw_inv, (h4 u w).1, neg_zero]
end Formalism.L2.Indef.ColData
