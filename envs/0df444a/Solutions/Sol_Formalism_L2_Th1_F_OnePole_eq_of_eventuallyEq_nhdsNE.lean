-- Prove2me | solution 1 for Formalism.L2.Th1.F.OnePole.eq_of_eventuallyEq_nhdsNE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:59.05375+00:00
-- url     : https://prove2.me/submissions/11da2cb9-568a-4b5b-b95a-461027494d50

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.OnePole
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.OnePole
theorem _root_.solution {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z := by
  exact tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
end Formalism.L2.Th1.F.OnePole
