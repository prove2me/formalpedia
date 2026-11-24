-- Prove2me | solution 1 for Formalism.L2.Indef.IndefColsR.D_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:46.103427+00:00
-- url     : https://prove2.me/submissions/ef10337a-1c50-4001-baaa-05101dba27a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefColsR_dQ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dQ_eq


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
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)
namespace Formalism.L2.Indef.IndefColsR
theorem _root_.solution : 0 < S.D := S.dQ_eq Bs.μ0 ▸ S.pos
end Formalism.L2.Indef.IndefColsR
