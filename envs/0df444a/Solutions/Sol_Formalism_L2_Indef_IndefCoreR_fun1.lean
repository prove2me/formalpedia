-- Prove2me | solution 1 for Formalism.L2.Indef.IndefCoreR.fun1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:46.186585+00:00
-- url     : https://prove2.me/submissions/1c3d7212-eb2c-4077-93ab-6f50816406ea

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
theorem _root_.solution (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3) :
    P.cols.muMaxRR ≤ N.hh - meanLog P.cols.κ + 14 * N.la := by
  rw [← P.extra.level.2.1]; exact (P.extra.passage hde hde3 _ P.extra.fun0).1
end Formalism.L2.Indef.IndefCoreR
