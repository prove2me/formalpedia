-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.T.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:06.300276+00:00
-- url     : https://prove2.me/submissions/ee3655e7-2ac1-4749-8aff-e21b53b4c1b8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
namespace T
theorem _root_.solution {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G)
    (h : f =ᶠ[𝓝[≠] 0] g) : F = G := by
  have hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f z = g z :=
    (hf.1.frequently_eq_iff_eventually_eq hg.1).1 h.frequently
  rw [← hf.2, ← hg.2]
  exact taylor_ring.2.2.2 f g hfg
end T
end Formalism.L2.Th1.F.EndoZ
