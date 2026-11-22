-- Prove2me | solution 1 for Formalism.L2.Indef.dim_of_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:34.955872+00:00
-- url     : https://prove2.me/submissions/993d7d55-3635-47d0-8931-d4bb3bfe2bdb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse

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
theorem _root_.solution {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) : d = d' := by
  have hb : Function.Bijective φ.mulVecLin := h
  have := (LinearEquiv.ofBijective φ.mulVecLin hb).finrank_eq
  simpa using this
end Formalism.L2.Indef
