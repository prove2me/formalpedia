-- Prove2me | solution 1 for Formalism.L2.Indef.IndefPkg2.mi0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:12:17.096053+00:00
-- url     : https://prove2.me/submissions/1d295ac6-40f0-445d-a135-0675e2aaddda

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
open Formalism.L2.Indef.IndefPkg2
variable {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
  (P : IndefPkg2 A fc cf C CH)
namespace Formalism.L2.Indef.IndefPkg2
theorem _root_.solution : P.core.cols.col.invZ.MatrixIdentityOffBase :=
  P.core.cols.col.inverse_matrix_identity_of_pairing P.core.cols.h0 P.core.cols.l1b
end Formalism.L2.Indef.IndefPkg2
