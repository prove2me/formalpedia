-- Prove2me | solution 1 for Formalism.L2.Indef.IndefPkg2.period_images_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:38:58.250007+00:00
-- url     : https://prove2.me/submissions/c5e61f0d-2a58-442c-972d-d6681b1c4678

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_ColData_period_images_surjective


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
theorem _root_.solution (hD : 0 < P.core.cols.D) (z : (fc P.Zs).Sp.HH) (hz : z ∈ (fc P.Zs).Sp.Rw) :
    ∃ y, P.core.cols.col.sE y = z :=
  P.core.cols.col.period_images_surjective P.core.cols.l1e (P.core.cols.frames.1 Bs.v0) hD z hz
end Formalism.L2.Indef.IndefPkg2
