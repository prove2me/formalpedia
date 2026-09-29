-- Prove2me | solution 1 for GaloisRep.DeformationRingData.comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/50478583-40a5-54c5-a99c-26ad1d823f84

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Theorems.Thm_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift

set_option autoImplicit false

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (S : Type) [CommRing S] [Algebra 𝒪 S] [IsLocalRing (TrivSqZeroExt S S)]
    [IsNoetherianRing (TrivSqZeroExt S S)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (TrivSqZeroExt S S)) (TrivSqZeroExt S S)]
    [IsLocalHom (algebraMap 𝒪 (TrivSqZeroExt S S))]
    (hres : Function.Surjective
      (IsLocalRing.residue (TrivSqZeroExt S S) ∘ algebraMap 𝒪 (TrivSqZeroExt S S)))
    (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪] S)
    (ψ : D'.R →ₐ[𝒪] TrivSqZeroExt S S) (hψ : IsLocalHom (ψ : D'.R →+* TrivSqZeroExt S S))
    (hsnd : ∀ (r : D'.R) (hr : r ∈ RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)),
      (ψ r).snd = φ ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).toCotangent ⟨r, hr⟩))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (ψ : D'.R →+* TrivSqZeroExt S S) hψ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (ψ : D'.R →+* TrivSqZeroExt S S) hψ)) :
    φ ∘ₗ (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
        (RingHom.ker x₀) θ (fun _ hr => hr))).subtype = 0 := by

  obtain ⟨ψ₀, -, hψ₀⟩ := GaloisRep.DeformationRingData.exists_algHom_comp_eq_of_isOfType D₀ D' θ hθ
    hθρ (TrivSqZeroExt S S) hres ψ hψ h𝒟' h𝒟₀
  have hkerθ : ∀ r : D'.R, θ r = 0 → ψ r = 0 := fun r hr => by
    rw [← hψ₀, AlgHom.comp_apply, hr, map_zero]

  have hI : RingHom.ker x₀ = Ideal.map θ (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)) := by
    refine le_antisymm (fun y hy => ?_) (Ideal.map_le_iff_le_comap.mpr fun r hr => ?_)
    · obtain ⟨r, rfl⟩ := hθsurj y
      exact Ideal.mem_map_of_mem θ (show r ∈ (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)) from hy)
    · exact hr
  have h2 : RingHom.ker x₀ ^ 2 = Ideal.map θ ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)) ^ 2) := by
    rw [Ideal.map_pow, hI]

  refine LinearMap.ext fun v => ?_
  obtain ⟨v, hv⟩ := v
  show φ v = 0
  obtain ⟨⟨r, hr⟩, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [LinearMap.mem_ker, Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero, h2] at hv
  obtain ⟨s, hs, hθs⟩ := (Ideal.mem_map_iff_of_surjective θ hθsurj).mp hv
  have hsK : s ∈ (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)) := Ideal.pow_le_self two_ne_zero hs
  have hrs : θ (r - s) = 0 := by rw [map_sub, hθs, sub_self]
  have hsplit : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).toCotangent ⟨r, hr⟩ =
      (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).toCotangent ⟨r - s, sub_mem hr hsK⟩ := by
    have e : (⟨r, hr⟩ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))) =
        ⟨r - s, sub_mem hr hsK⟩ + ⟨s, hsK⟩ := by
      ext; simp
    rw [e, map_add, (Ideal.toCotangent_eq_zero _ ⟨s, hsK⟩).mpr hs, add_zero]
  rw [hsplit, ← hsnd (r - s) (sub_mem hr hsK), hkerθ (r - s) hrs, TrivSqZeroExt.snd_zero]

end S_GaloisRep_DeformationRingData_comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift (solution)
