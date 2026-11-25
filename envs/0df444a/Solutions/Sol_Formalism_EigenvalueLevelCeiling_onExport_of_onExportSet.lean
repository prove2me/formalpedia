-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.onExport_of_onExportSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:55.278793+00:00
-- url     : https://prove2.me/submissions/acab797c-5641-470d-880a-69eae1dd195b

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (h : OnExportSet) : OnExport := by
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10
  obtain ⟨-, hA, hB, hC⟩ := h K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3
    h4 h5 (fun w hw => by
    have hw6 := h6 w hw
    have hp : 0 ≤ 1 / (plc w : ℝ) ^ 2 := by positivity
    by_cases hc : conjPl w = w
    · simp only [if_pos hc, add_zero]
      rw [hc, Finset.sum_add_distrib] at hw6
      by_cases hs : 0 ≤ ∑ j, ε0 w j
      · linarith
      · push_neg at hs
        linarith
    · simp only [if_neg hc]
      exact hw6) h7 h8 h9 h10
  exact ⟨hA, hB, hC⟩
end Formalism.EigenvalueLevelCeiling
