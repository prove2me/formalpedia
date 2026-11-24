-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.sum_le_named
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:54.482805+00:00
-- url     : https://prove2.me/submissions/55766aab-f396-45ce-9f25-625056c023ea

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_total_named_real
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_d0
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_sum_split
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_levels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Formalism.MainNotions.Gaps.T0.SumDat
variable {ι : Type*} (X : SumDat ι)
variable {X}
namespace Formalism.MainNotions.Gaps.T0.SumDat
namespace Ok
theorem _root_.solution (h : X.Ok) : ∑ la ∈ X.s, X.rr la * X.l la ≤ X.totalNamed := by
  rw [sum_split]
  have hL := h.levels
  have key := total_named_real (fr := X.f * X.r ^ 2) (Pη := X.Pη) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h.d0 h.D1 h.T1 h.G0 h.height_param_nonneg h.BaseRankDimension h.quotient_param_nonneg h.κ0 h.S2 (Real.log_nonneg h.δ1) h.lδ h.shρ h.shρ'
  unfold SumDat.totalNamed SumDat.P1 SumDat.P2 SumDat.P3 SumDat.P4
  unfold SumDat.lev at hL
  linarith [h.deep, h.quot]
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
