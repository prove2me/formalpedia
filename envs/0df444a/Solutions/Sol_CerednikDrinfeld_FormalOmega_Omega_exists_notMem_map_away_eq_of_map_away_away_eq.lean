-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.exists_notMem_map_away_eq_of_map_away_away_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7f831305-ff00-539a-aaa1-39ae90cc6ea4

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_notMem_map_away_eq_of_map_away_away_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime)
    (e : B) (he : e ∉ 𝔭) (f : Localization.Away e) (hf : f ∉ Ideal.map (algebraMap B (Localization.Away e)) 𝔭)
    (P P' : (Omega K₀ π).obj B)
    (h : (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 (Localization.Away e) (Localization.Away f))
            ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away e)) P)
       = (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 (Localization.Away e) (Localization.Away f))
            ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away e)) P')) :
    ∃ c : B, c ∉ 𝔭 ∧ (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) P
      = (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) P' := by
  classical

  obtain ⟨k, y, hfy⟩ := IsLocalization.Away.surj e f

  have hy : y ∉ 𝔭 := by
    intro hy
    apply hf
    have hu : IsUnit (algebraMap B (Localization.Away e) e ^ k) :=
      (IsLocalization.Away.algebraMap_isUnit e).pow k
    have hf' : f = algebraMap B (Localization.Away e) y * ↑hu.unit⁻¹ := by
      rw [← hfy, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [hf']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy)
  refine ⟨e * y, ?_, ?_⟩
  · intro hmem
    rcases h𝔭.mem_or_mem hmem with h1 | h2
    · exact he h1
    · exact hy h2

  have hc : IsUnit (algebraMap B (Localization.Away (e * y)) (e * y)) :=
    IsLocalization.Away.algebraMap_isUnit (e * y)
  rw [map_mul] at hc
  have hce : IsUnit (algebraMap B (Localization.Away (e * y)) e) := isUnit_of_mul_isUnit_left hc
  have hcy : IsUnit (algebraMap B (Localization.Away (e * y)) y) := isUnit_of_mul_isUnit_right hc
  have hσu : ∀ m : ↥(Submonoid.powers e),
      IsUnit ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (e * y))) (m : B)) := by
    intro m
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
    rw [IsScalarTower.coe_toAlgHom', ← hn, map_pow]
    exact hce.pow n
  let σ : Localization.Away e →ₐ[𝒪] Localization.Away (e * y) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers e) hσu
  have hσ : ∀ b : B, σ (algebraMap B (Localization.Away e) b) = algebraMap B (Localization.Away (e * y)) b := by
    intro b
    show IsLocalization.lift _ (algebraMap B (Localization.Away e) b) = _
    rw [IsLocalization.lift_eq]
    rfl
  have hσf : IsUnit (σ f) := by
    have hmul : σ f * σ (algebraMap B (Localization.Away e) e ^ k) = algebraMap B (Localization.Away (e * y)) y := by
      rw [← map_mul, hfy, hσ]
    have : IsUnit (σ f * σ (algebraMap B (Localization.Away e) e ^ k)) := hmul ▸ hcy
    exact isUnit_of_mul_isUnit_left this
  have hτu : ∀ m : ↥(Submonoid.powers f), IsUnit (σ (m : Localization.Away e)) := by
    intro m
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
    rw [← hn, map_pow]
    exact hσf.pow n
  let τ : Localization.Away f →ₐ[𝒪] Localization.Away (e * y) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers f) hτu
  have hτ : τ.comp ((IsScalarTower.toAlgHom 𝒪 (Localization.Away e) (Localization.Away f)).comp
      (IsScalarTower.toAlgHom 𝒪 B (Localization.Away e))) =
      IsScalarTower.toAlgHom 𝒪 B (Localization.Away (e * y)) := by
    apply AlgHom.ext
    intro b
    show τ (algebraMap (Localization.Away e) (Localization.Away f) (algebraMap B (Localization.Away e) b)) =
      algebraMap B (Localization.Away (e * y)) b
    show IsLocalization.lift _ (algebraMap (Localization.Away e) (Localization.Away f) (algebraMap B (Localization.Away e) b)) = _
    rw [IsLocalization.lift_eq]
    exact hσ b
  rw [← hτ, (Omega K₀ π).map_comp, (Omega K₀ π).map_comp, (Omega K₀ π).map_comp, (Omega K₀ π).map_comp, h]

end S_CerednikDrinfeld_FormalOmega_Omega_exists_notMem_map_away_eq_of_map_away_away_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_notMem_map_away_eq_of_map_away_away_eq (solution)
