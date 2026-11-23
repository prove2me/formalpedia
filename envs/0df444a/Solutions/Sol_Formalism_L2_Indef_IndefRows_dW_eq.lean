-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.dW_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:12.74101+00:00
-- url     : https://prove2.me/submissions/916e28f0-85a3-4228-9683-731939e1304e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_sum_finrank
import Theorems.Thm_Formalism_L2_Indef_map_indep
import Theorems.Thm_Formalism_L2_Indef_map_iSup_top

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
theorem _root_.solution (wf : Df.WF) (j : Bs.J) : S.dW j = S.D := by
  have hb0 := S.l1c.1 Bs.μ0
  have hθ0 := S.l1c.2.1 j Bs.μ0
  have he : S.Ep = fun p => (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.1 p).symm
  have hw : S.Wp j = fun p => (Df.Zp j Bs.μ0 p).map (S.θ j Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.2 j p).symm
  have a := sum_finrank (S.Wp j) (by rw [hw]; exact map_indep _ hθ0 _ (wf.Zp_indep j))
    (by rw [hw]; exact map_iSup_top _ hθ0 _ (S.4 j))
  have b := sum_finrank S.Ep (by rw [he]; exact map_indep _ hb0 _ wf.Qp_indep)
    (by rw [he]; exact map_iSup_top _ hb0 _ wf.Qp_top)
  first
  | simp only [Module.finrank_fin_fun] at a b
  | simp at a b
  calc S.dW j = ∑ p, finrank K (S.Wp j p) := a.symm
    _ = ∑ p, finrank K (S.Ep p) := Finset.sum_congr rfl fun p _ => S.l1d j p
    _ = S.D := b
end Formalism.L2.Indef.IndefRows
