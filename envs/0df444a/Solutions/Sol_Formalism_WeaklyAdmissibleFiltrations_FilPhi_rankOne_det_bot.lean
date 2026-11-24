-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_det_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:40:31.393665+00:00
-- url     : https://prove2.me/submissions/fc0e06d4-6b30-4de3-9b0c-f4d2cdf6775c

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
theorem _root_.solution (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊥ : Submodule LL D), F.φ x ∈ (⊥ : Submodule LL D)) :
    LinearMap.det (F.φres ⊥ h) = 1 :=
  LinearMap.det_eq_one_of_subsingleton _
end Formalism.WeaklyAdmissibleFiltrations.FilPhi
