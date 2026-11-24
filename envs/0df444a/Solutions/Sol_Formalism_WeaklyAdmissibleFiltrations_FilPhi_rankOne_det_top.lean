-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_det_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:40:48.753082+00:00
-- url     : https://prove2.me/submissions/b91d77b7-b8e6-43e6-9c54-4e8af6cbe09a

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne

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
open Module
open Formalism.WeaklyAdmissibleFiltrations.FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations.FilPhi
theorem _root_.solution (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊤ : Submodule LL D), F.φ x ∈ (⊤ : Submodule LL D)) :
    LinearMap.det (F.φres ⊤ h) = LinearMap.det (F.φ : D →ₗ[LL] D) := by
  have hc : (F.φ : D →ₗ[LL] D) = (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).toLinearMap ∘ₗ
      F.φres ⊤ h ∘ₗ (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).symm.toLinearMap := by
    ext x; rfl
  rw [hc, LinearMap.det_conj]
end Formalism.WeaklyAdmissibleFiltrations.FilPhi
