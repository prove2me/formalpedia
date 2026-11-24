-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.torsFreeT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:10.329341+00:00
-- url     : https://prove2.me/submissions/2169fd46-e220-4272-b519-6aa0efa12ac8

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : TorsFreeT := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V _ _ _ _ _ _ ρ
    _ _ _ _ L c a hc ha h
  refine ⟨hc, ?_⟩
  have h2 : (algebraMap O LL a) • c ∈ finiteCocycles PD ρ := by
    rw [algebraMap_smul]
    exact h.2
  have h3 := (finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h2
  rw [inv_smul_smul₀ ha] at h3
  exact h3
end Formalism.WeaklyAdmissibleFiltrations
