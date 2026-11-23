-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.haarExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:00.181065+00:00
-- url     : https://prove2.me/submissions/dc5391e7-bb08-4aca-a7b7-31cef827d5ba

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_haar_closed
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_upUni_closed
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_lowW_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.HaarExists := by
  intro K _ _ _ _ _ R hRo hRc ⟨ϖ, hϖ, hx⟩ s t
  refine ⟨haar_closed R hRo hRc ϖ hϖ hx (lowW K s t) (lowW_closed s t)
    (fun a => s.sum - a.val) ?_, haar_closed R hRo hRc ϖ hϖ hx (upUniG K s.sum)
    (upUni_closed s.sum) Fin.val ?_⟩
  · intro g hg a b
    rcases lt_trichotomy a b with h | rfl | h
    · left; exact hg.1.1 (by simpa using h)
    · right; left; exact ⟨rfl, hg.1.2 a⟩
    · right; right
      have := a.2; have := b.2
      have : b.val < a.val := h
      show s.sum - a.val < s.sum - b.val
      omega
  · intro g hg a b
    rcases lt_trichotomy a b with h | rfl | h
    · right; right; exact h
    · right; left; exact ⟨rfl, hg.2 a⟩
    · left; exact hg.1 h
end Formalism.DoubleCosetMeasures.P
