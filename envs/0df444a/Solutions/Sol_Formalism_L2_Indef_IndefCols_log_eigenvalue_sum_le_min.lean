-- Prove2me | solution 1 for Formalism.L2.Indef.IndefCols.log_eigenvalue_sum_le_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:42.390131+00:00
-- url     : https://prove2.me/submissions/6a83fb6f-3eef-49be-9f05-8dbc4c1392f0

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
namespace IndefCols
theorem _root_.solution {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    [Nonempty Bs.Ix] (S : IndefCols Df Dc Sp N) (v : InfinitePlace K) :
    ∑ j, N.l6 j ≤ minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) :=
  Finset.le_inf' _ _ fun p _ => Finset.sum_le_sum fun j _ => S.l6 j p v
end IndefCols
end Formalism.L2.Indef
