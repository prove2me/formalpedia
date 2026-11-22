-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.Qpart_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:01.223987+00:00
-- url     : https://prove2.me/submissions/89a95721-1667-4407-825f-2c4f990a7d9b

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
open Formalism.L2.Indef.IndefRows
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df)
include S
namespace Formalism.L2.Indef.IndefRows
theorem _root_.solution (p : Bs.Ix) : S.Qpart Bs.μ0 p = Df.Qp Bs.μ0 p := by
  have hb : Function.Bijective (S.ι Bs.μ0).mulVecLin := S.l1c.1 Bs.μ0
  show (S.Ep p).comap (S.ι Bs.μ0).mulVecLin = _
  rw [← S.l1a.1 p, Submodule.comap_map_eq_of_injective hb.1]
end Formalism.L2.Indef.IndefRows
