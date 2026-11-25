-- Prove2me | solution 1 for Formalism.L2.Indef.IndefCoreR.base_level_log_eigenvalue_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:35.692913+00:00
-- url     : https://prove2.me/submissions/4e1caa1e-a077-4701-b61c-ce2c001f6882

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity

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
open Formalism.L2.Indef.IndefCoreR
variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCoreR Df0 Df1 Dc Sp N)
include P
namespace Formalism.L2.Indef.IndefCoreR
theorem _root_.solution : P.base.toIndefData.L6 N := fun j p v => by
  rw [P.extra.level.2.2]; exact P.cols.l6 j p v
end Formalism.L2.Indef.IndefCoreR
