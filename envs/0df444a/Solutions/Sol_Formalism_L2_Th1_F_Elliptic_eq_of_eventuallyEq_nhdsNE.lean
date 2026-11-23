-- Prove2me | solution 1 for Formalism.L2.Th1.F.Elliptic.eq_of_eventuallyEq_nhdsNE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:03.222447+00:00
-- url     : https://prove2.me/submissions/daefaec2-ba6e-428b-a271-3a2825519e16

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic

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
open Formalism.L2.Th1.F.Elliptic
namespace Formalism.L2.Th1.F.Elliptic
theorem _root_.solution {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z :=
  tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
end Formalism.L2.Th1.F.Elliptic
