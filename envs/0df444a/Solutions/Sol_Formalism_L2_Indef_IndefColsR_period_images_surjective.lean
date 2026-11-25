-- Prove2me | solution 1 for Formalism.L2.Indef.IndefColsR.period_images_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:21:22.567234+00:00
-- url     : https://prove2.me/submissions/22c5cbb4-f1f3-4a44-922e-c62c531bbec1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefPkg2_period_images_surjective
import Theorems.Thm_Formalism_L2_Indef_IndefColsR_D_pos
import Theorems.Thm_Formalism_L2_Indef_ColData_period_images_surjective
import Theorems.Thm_Formalism_L2_Indef_IndefRows_D_pos


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
    (S : IndefColsR Df Dc Sp N) (z : Sp.HH) (hz : z ∈ Sp.Rw) : ∃ y, S.col.sE y = z :=
  S.col.period_images_surjective S.l1e (S.frames Bs.v0) S.D_pos z hz
end IndefColsR
end Formalism.L2.Indef
