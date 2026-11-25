-- Prove2me | solution 1 for Formalism.L2.Indef.IndefPkg2.tuple_is_base_or_member
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:12:23.732955+00:00
-- url     : https://prove2.me/submissions/cc6f4882-309f-45f4-be46-c1c3ce5daf1a

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
open Formalism.L2.Indef.IndefPkg2
variable {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
  (P : IndefPkg2 A fc cf C CH)
namespace Formalism.L2.Indef.IndefPkg2
theorem _root_.solution : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.core.cols.μ w = t := by
  intro t
  rcases P.conv.c2 t with h | ⟨w, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, by rw [← P.core.extra.level.1]; exact hw⟩
end Formalism.L2.Indef.IndefPkg2
