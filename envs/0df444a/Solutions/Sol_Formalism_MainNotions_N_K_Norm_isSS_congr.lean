-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.isSS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:25.466402+00:00
-- url     : https://prove2.me/submissions/719b2115-4aec-49fc-b161-13277393cd83

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (h : IsSS ρ) : IsSS ρ' := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h (W.comap (e : V →ₗ[Kf] V')) (fun g v hv => by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, he] at hv ⊢
    exact hW g _ hv)
  refine ⟨W'.map (e : V →ₗ[Kf] V'), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hW' g v hv, he g v⟩
  · have h1 : IsCompl ((W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V')) (W'.map (e : V →ₗ[Kf] V')) :=
      (Submodule.orderIsoMapComap e).isCompl_iff.1 hc
    have h2 : (W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V') = W :=
      Submodule.map_comap_eq_of_surjective e.surjective W
    rw [h2] at h1
    exact h1
end Formalism.MainNotions.N.K.Norm
