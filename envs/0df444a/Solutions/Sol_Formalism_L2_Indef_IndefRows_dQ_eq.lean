-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.dQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:37.669804+00:00
-- url     : https://prove2.me/submissions/d0fb0336-7065-49d9-9323-4c1f4bd337fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_dim_of_bij

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
theorem _root_.solution (t : Bs.Tup) : Df.dQ t = S.D := dim_of_bij (S.ι t) (S.l1c.1 t)
end Formalism.L2.Indef.IndefRows
