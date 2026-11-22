-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.large_x_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:58.996956+00:00
-- url     : https://prove2.me/submissions/0ea92ba9-c9a8-4999-9129-98598f131900

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution : LargeXEv := by
  intro ε K cHH eK hε
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ ε := by
    have hb := (isLittleO_log_rpow_atTop hε).bound (c := 1) one_pos
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact (le_abs_self _).trans hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, KBig K cHH eK ≤ x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and h2)
  exact ⟨x0, fun x hx => hx0 x hx⟩
end Formalism.LFunctionChainParameters.LErr
