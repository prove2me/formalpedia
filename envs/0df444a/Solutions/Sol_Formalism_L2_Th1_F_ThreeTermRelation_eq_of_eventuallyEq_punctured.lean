-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.eq_of_eventuallyEq_punctured
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:50.546504+00:00
-- url     : https://prove2.me/submissions/112f8f58-cf47-4339-aef5-4826a5bc5314

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero

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
open Formalism.L2.Th1.F.ThreeTermRelation
namespace Formalism.L2.Th1.F.ThreeTermRelation
theorem _root_.solution {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (h : f =ᶠ[𝓝[≠] z] g) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
end Formalism.L2.Th1.F.ThreeTermRelation
