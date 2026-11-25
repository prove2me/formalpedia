-- Prove2me | solution 1 for Formalism.L2.Indef.ColData.pairing_iff_inverse_matrix_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:09:01.517667+00:00
-- url     : https://prove2.me/submissions/b3748bc8-b023-4f5d-aeec-dad0f8c3646e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_B
import Theorems.Thm_P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_sE
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_invZ
import Theorems.Thm_Formalism_L2_Indef_ColData_pairing_condition_of_inverse_matrix_identity
import Theorems.Thm_Formalism_L2_Indef_ColData_inverse_matrix_identity_of_pairing
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
theorem _root_.solution (h0 : S.H0) : C.PairingFactorsThroughPeriods ↔ C.invZ.MatrixIdentityOffBase :=
  ⟨C.inverse_matrix_identity_of_pairing h0, fun h => by simpa only [invZ_invZ] using C.invZ.pairing_condition_of_inverse_matrix_identity h⟩
end Formalism.L2.Indef.ColData
