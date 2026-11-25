-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.absIrrDistinct_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:19.787994+00:00
-- url     : https://prove2.me/submissions/fc8a0408-2739-4b81-a57f-7458d3d56c3e

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerCharAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerChar_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFinitenessAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFiniteness_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDualityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDuality_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonalityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonality_restrict
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
theorem _root_.solution (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by
  obtain ⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩ := h
  let Vs' : ι → Submodule Kf V' := fun j => (Vs j).map (e : V →ₗ[Kf] V')
  have hs' : ∀ j, Stable ρ' (Vs' j) := by
    rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hs j g v hv, he g v⟩
  let ej : ∀ j, Vs j ≃ₗ[Kf] Vs' j := fun j => e.submoduleMap (Vs j)
  have hej : ∀ j g (v : Vs j), ej j ((ρ g).restrict (hs j g) v) = (ρ' g).restrict (hs' j g) (ej j v) := by
    intro j g v
    apply Subtype.ext
    exact he g v
  refine ⟨ι, hι, hd, Vs', hs', ?_, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    obtain ⟨hind, htop⟩ := hint
    refine ⟨hind.map_orderIso (Submodule.orderIsoMapComap e), ?_⟩
    show ⨆ j, (Vs j).map (e : V →ₗ[Kf] V') = ⊤
    rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearEquiv.range]
  · intro j hj
    apply hne j
    have h1 := congrArg (Submodule.comap (e : V →ₗ[Kf] V')) hj
    rwa [Submodule.comap_map_eq_of_injective e.injective, Submodule.comap_bot, LinearEquiv.ker] at h1
  · intro j
    let c : Module.End Kf (Vs j) ≃ₗ[Kf] Module.End Kf (Vs' j) := LinearEquiv.conj (ej j)
    have hc : ∀ g, c ((ρ g).restrict (hs j g)) = (ρ' g).restrict (hs' j g) := by
      intro g
      apply LinearMap.ext
      intro v
      rw [LinearEquiv.conj_apply]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hej, LinearEquiv.apply_symm_apply]
    have hr : Set.range (fun g => (ρ' g).restrict (hs' j g)) =
        (c : Module.End Kf (Vs j) →ₗ[Kf] Module.End Kf (Vs' j)) '' Set.range (fun g => (ρ g).restrict (hs j g)) := by
      ext f
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨_, ⟨g, rfl⟩, hc g⟩
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, (hc g).symm⟩
    rw [hr, ← Submodule.map_span, hspan j, Submodule.map_top, LinearEquiv.range]
  · intro j j' hjj f hf
    apply hdist j j' hjj (((ej j).trans f).trans (ej j').symm)
    intro g v
    simp only [LinearEquiv.trans_apply]
    rw [hej, hf]
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (ej j') (f (ej j v)), ← hej, LinearEquiv.symm_apply_apply]
end Formalism.MainNotions.N.K.Norm
