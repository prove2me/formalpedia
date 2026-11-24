-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.Ep_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:13:12.923633+00:00
-- url     : https://prove2.me/submissions/16b375e2-f9ea-430d-80a1-cbc7775a066d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
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
theorem _root_.solution (wf : Df.WF) : iSupIndep S.Ep ∧ (⨆ p, S.Ep p) = ⊤ := by
  have hb0 := S.l1c.1 Bs.μ0
  have he : S.Ep = fun p => (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.1 p).symm
  rw [he]
  exact ⟨map_indep _ hb0 _ wf.Qp_indep, map_iSup_top _ hb0 _ wf.Qp_top⟩
end Formalism.L2.Indef.IndefRows
