-- Prove2me | solution 1 for Formalism.L2.Indef.ColData.inverse_matrix_identity_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:02.469585+00:00
-- url     : https://prove2.me/submissions/f80546c5-7837-49dc-aad1-95a5a2f2a50a

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
theorem _root_.solution (h0 : S.H0) (h : C.PairingFactorsThroughPeriods) : C.invZ.MatrixIdentityOffBase := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u t φ F => ?_, fun u => ?_, fun u t => ?_, fun u w => ⟨?_, ?_⟩⟩
  · simp only [invZ_ζ, invZ_B]
    rw [h1 u t φ F, ← mul_assoc, inv_mul_cancel₀ (h3 u t), one_mul]
  · simp [h2 u]
  · simpa using h3 u t
  · simp only [invZ_ζ]
    rw [vw_inv, h4 u w, neg_zero]
  · simp only [invZ_ζ]
    have := h4 u (conjPl w)
    rw [h0.1 w] at this
    rw [vw_inv, this, neg_zero]
end Formalism.L2.Indef.ColData
