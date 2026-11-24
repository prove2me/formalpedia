-- Prove2me | solution 1 for Formalism.GM.windowFullAP_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:28.765945+00:00
-- url     : https://prove2.me/submissions/1a92e946-2782-4d3f-b17c-755316b58783

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Theorems.Thm_Formalism_GM_ProgressionMeanBounds_binMatK_det_natDegree_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial ProgressionMeanBounds
namespace Formalism.GM
theorem _root_.solution (hL : ValuationWindowLowerBound) (hW : WindowMeanAP) : WindowFullAP := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ d Y₀ La₀ U V dg hd hY hYp hdel hE hlead hc hdet hj hlam
  have hcard : roots.card ≤ del₀ * n := by
    have e : ((binMatK K del₀ c).det).natDegree = roots.card := by
      rw [hdet, natDegree_C_mul hlead, natDegree_multiset_prod_X_sub_C_eq_card]
    rw [← e]
    exact binMatK_det_natDegree_le K del₀ c
  refine hW p K roots (-Real.logb p ‖lead‖) La₀ E n del₀ t₀ d Y₀ h
    (fun t => (univ.filter (fun i => ‖dg t i‖ ≤ (p : ℝ) ^ (-E))).card) hd hY hYp hE hcard hlam ?_
  intro j hjr
  obtain ⟨hU, hV, hdU, hdV, hmap⟩ := hj j hjr
  exact hL p K n del₀ h E c lead roots (progr t₀ d j) (U (progr t₀ d j)) (V (progr t₀ d j))
    (dg (progr t₀ d j)) hc hU hV hdU hdV hE.le hdel hlead hdet hmap
end Formalism.GM
