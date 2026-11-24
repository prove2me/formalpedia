-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.detId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:08.453534+00:00
-- url     : https://prove2.me/submissions/9179148e-c276-4a14-af47-cd0be9fbc871

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_IndefRows_part_dim
import Theorems.Thm_Formalism_L2_Indef_IndefRows_Qpart_decomp
import Theorems.Thm_Formalism_L2_Indef_IndefRows_Zpart_decomp
import Theorems.Thm_Formalism_L2_Indef_specDet_rect

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
namespace IndefRows
theorem _root_.solution (hS : SpecDet) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF)
    (S : IndefRows Df) (t : Bs.Tup) (v : InfinitePlace K) (h : t = Bs.μ0 ∨ v = Bs.v0) :
    detRatio (Df.XQ t) S.XE (S.ι t) v =
      S.κ v ^ S.D * ∏ j, detRatio (Df.XT j t) (S.XW j) (S.θ j t) v :=
  specDet_rect hS v (Df.XQ t) S.XE (fun u => (wf.XQ_quot t u).1) S.frames.1 (S.ι t) (S.l1c.1 t) Bs.J
    (fun j => Df.dZ j t) S.dW (fun j => Df.XT j t) S.XW (fun j => (wf.XT_herm j t).1) S.frames.2.1
    (fun j => S.θ j t) (fun j => S.l1c.2.1 j t) Bs.Ix (S.Qpart t) (fun j => S.Zpart j t) (S.Qpart_decomp wf t).1
    (S.Qpart_decomp wf t).2 (fun j => (S.Zpart_decomp wf j t).1) (fun j => (S.Zpart_decomp wf j t).2)
    (fun j p => S.part_dim j t p)
    (S.κ v) (fun j p => S.lam j t p v) (S.l1c.2.2.2.2.1 t v h) (fun j => S.l1c.2.2.2.2.2 j t v h)
end IndefRows
end Formalism.L2.Indef
