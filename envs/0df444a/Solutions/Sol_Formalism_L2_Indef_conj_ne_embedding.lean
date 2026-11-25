-- Prove2me | solution 1 for Formalism.L2.Indef.conj_ne_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:04.542389+00:00
-- url     : https://prove2.me/submissions/a946ecf8-0ec9-4d81-b6fc-1e474d24fc9c

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
namespace Formalism.L2.Indef
theorem _root_.solution (v : InfinitePlace K) (hv : v.IsComplex) :
    ComplexEmbedding.conjugate v.embedding ≠ v.embedding := by
  intro h
  exact (InfinitePlace.isComplex_iff.1 hv) (ComplexEmbedding.isReal_iff.2 h)
end Formalism.L2.Indef
