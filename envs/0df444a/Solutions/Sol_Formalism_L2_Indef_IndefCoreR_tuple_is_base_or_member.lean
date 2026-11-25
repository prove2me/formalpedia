-- Prove2me | solution 1 for Formalism.L2.Indef.IndefCoreR.tuple_is_base_or_member
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:52.039736+00:00
-- url     : https://prove2.me/submissions/1acba07f-14cb-452b-9ffa-89d174ad2cc8

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
theorem _root_.solution (h : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.base.μ w = t) : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.cols.μ w = t := by
  intro t
  rcases h t with h | ⟨w, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, by rw [← P.extra.level.1]; exact hw⟩
end Formalism.L2.Indef.IndefCoreR
