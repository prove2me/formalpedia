-- Prove2me | solution 1 for Formalism.L2.Indef.ColData.invZ_invZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:41.754099+00:00
-- url     : https://prove2.me/submissions/8d256913-4f45-4ab5-8c61-4aaaaf5626d4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
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
theorem _root_.solution : C.invZ.invZ = C := by
  cases C
  simp only [invZ, inv_inv]
end Formalism.L2.Indef.ColData
