-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.part_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:38.428078+00:00
-- url     : https://prove2.me/submissions/329468cf-927c-4b99-83f2-762eff2379a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_finrank_comap_bij

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
theorem _root_.solution (j : Bs.J) (t : Bs.Tup) (p : Bs.Ix) :
    finrank K (S.Qpart t p) = finrank K (S.Zpart j t p) := by
  show finrank K ((S.Ep p).comap (S.ι t).mulVecLin) = finrank K ((S.Wp j p).comap (S.θ j t).mulVecLin)
  rw [finrank_comap_bij _ (S.l1c.1 t), finrank_comap_bij _ (S.l1c.2.1 j t), S.l1d j p]
end Formalism.L2.Indef.IndefRows
