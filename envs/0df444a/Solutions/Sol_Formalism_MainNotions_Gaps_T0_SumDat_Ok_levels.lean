-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.levels
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.154779+00:00
-- url     : https://prove2.me/submissions/eb036288-8e65-482e-ab2e-0ca4fe66a8af

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_levels_real

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
theorem _root_.solution (h : X.Ok) :
    X.R * (∑ la ∈ X.s, X.I la * X.l la + 1 / 2 * (X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la)) ≤
      X.d * X.lev := by
  have hδ0 : 0 ≤ X.δ := by linarith [h.δ1]
  have hw0 : 0 ≤ Real.log X.rw + 1 / 2 := by linarith [Real.log_nonneg h.rw1]
  have hw : Real.log X.rw + 1 / 2 ≤ X.PH * X.L := h.lrw.trans (mul_le_mul_of_nonneg_right h.PrwPH h.L0)
  have hcg0 : 0 ≤ X.T * X.c * X.g₀ := mul_nonneg (mul_nonneg (by linarith [h.T1]) h.c0) h.g0
  have key := levels_real _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.R0 h.Rδ hδ0
    (Real.log_nonneg h.δ1) (by linarith [h.D1]) (by linarith [h.T1]) h.c0 hcg0 h.Tcg hw0 hw h.G0 h.height_param_nonneg
    h.Pη0 h.L0 (mul_nonneg h.f0 (sq_nonneg X.r)) h.lev1 h.lev2 h.SSle h.S4 h.S3 h.aδle h.aFle h.HFle h.Hδle
  unfold SumDat.lev
  exact key
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
