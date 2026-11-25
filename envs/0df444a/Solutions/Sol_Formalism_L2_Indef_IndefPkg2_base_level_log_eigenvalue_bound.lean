-- Prove2me | solution 1 for Formalism.L2.Indef.IndefPkg2.base_level_log_eigenvalue_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:57.435886+00:00
-- url     : https://prove2.me/submissions/c90b36ea-3a6d-45ed-a2b0-edddd286c468

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefCore_base_level_log_eigenvalue_bound


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
theorem _root_.solution : P.core.base.toIndefData.L6 ((fc P.Zs).Z.num C CH) := P.core.base_level_log_eigenvalue_bound
end Formalism.L2.Indef.IndefPkg2
