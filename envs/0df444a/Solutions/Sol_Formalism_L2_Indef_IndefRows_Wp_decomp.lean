-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.Wp_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:29.314013+00:00
-- url     : https://prove2.me/submissions/40952a0d-7ce7-40ff-b059-178386db04fa

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
theorem _root_.solution (wf : Df.WF) (j : Bs.J) : iSupIndep (S.Wp j) ∧ (⨆ p, S.Wp j p) = ⊤ := by
  have hθ0 := S.l1c.2.1 j Bs.μ0
  have hw : S.Wp j = fun p => (Df.Zp j Bs.μ0 p).map (S.θ j Bs.μ0).mulVecLin :=
    funext fun p => (S.l1a.2 j p).symm
  rw [hw]
  exact ⟨map_indep _ hθ0 _ (wf.Zp_indep j), map_iSup_top _ hθ0 _ (S.4 j)⟩
end Formalism.L2.Indef.IndefRows
