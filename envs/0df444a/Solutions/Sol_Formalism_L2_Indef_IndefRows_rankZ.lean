-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.rankZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:30.641385+00:00
-- url     : https://prove2.me/submissions/58ecfa23-fbe8-4d7e-b419-80a7916ccc6b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dZ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dW_eq

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
open Formalism.L2.Indef.IndefRows
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df)
include S
namespace Formalism.L2.Indef.IndefRows
theorem _root_.solution (wf : Df.WF) (j : Bs.J) (t : Bs.Tup) : Df.dZ j t = S.D := by
  rw [S.dZ_eq j t, S.dW_eq wf j]
end Formalism.L2.Indef.IndefRows
