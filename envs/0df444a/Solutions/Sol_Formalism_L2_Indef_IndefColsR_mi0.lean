-- Prove2me | solution 1 for Formalism.L2.Indef.IndefColsR.mi0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:23.932252+00:00
-- url     : https://prove2.me/submissions/1c261a1d-4155-4a9f-aff4-7c72e36192c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_ColData_inverse_matrix_identity_of_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
namespace IndefColsR
theorem _root_.solution {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (S : IndefColsR Df Dc Sp N) : S.col.invZ.MatrixIdentityOffBase :=
  S.col.inverse_matrix_identity_of_pairing S.h0 S.l1b
end IndefColsR
end Formalism.L2.Indef
