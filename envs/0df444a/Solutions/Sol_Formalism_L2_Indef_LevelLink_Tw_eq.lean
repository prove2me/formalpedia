-- Prove2me | solution 1 for Formalism.L2.Indef.LevelLink.Tw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:15:37.217559+00:00
-- url     : https://prove2.me/submissions/917671e0-ea2a-436a-9b78-d753dd03291b

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
namespace LevelLink
theorem _root_.solution {Bs : DefBase K} {Df Df' : DefSide Bs} {S : IndefData Df} {S' : IndefData Df'}
    (h : LevelLink S S') (h0 : S.H0) (h0' : S'.H0) : S.Tw = S'.Tw := by
  ext w
  rw [h0.2 w, h0'.2 w, h.1]
end LevelLink
end Formalism.L2.Indef
