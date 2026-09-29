-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/08115ffa-55fe-5725-b900-047d62b68947

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace KerDegComp

variable {B : Type} [CommRing B]

theorem comp_apply (ψ φ : Series B) (i : Fin 2) : (ψ.comp φ) i = MvPowerSeries.subst φ (ψ i) := rfl

theorem subst_mem_span_comp {ψ φ : Series B} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    {c : MvPowerSeries (Fin 2) B} (hc : c ∈ Ideal.span (Set.range ψ)) :
    MvPowerSeries.subst φ c ∈ Ideal.span (Set.range (ψ.comp φ)) := by
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  let F : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B :=
    (MvPowerSeries.substAlgHom hsub : MvPowerSeries (Fin 2) B →ₐ[B] _).toRingHom
  have hF : ∀ g, F g = MvPowerSeries.subst φ g := fun g => by
    show (MvPowerSeries.substAlgHom hsub) g = _; rw [← MvPowerSeries.coe_substAlgHom hsub]
  have h1 : (Ideal.span (Set.range ψ)).map F ≤ Ideal.span (Set.range (ψ.comp φ)) := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hF]
    exact Ideal.subset_span ⟨i, rfl⟩
  have h2 := h1 (Ideal.mem_map_of_mem F hc)
  rwa [hF] at h2

theorem exists_X_pow_mem_comp {ψ φ : Series B} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    {Nφ Nψ : ℕ} (hNφ : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ Nφ ∈ Ideal.span (Set.range φ))
    (hNψ : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ Nψ ∈ Ideal.span (Set.range ψ)) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range (ψ.comp φ)) := by
  classical
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0

  let I := Ideal.span (Set.range (ψ.comp φ))
  let mk := Ideal.Quotient.mk I
  have hφnil : ∀ j, IsNilpotent (mk (φ j)) := fun j => ⟨Nψ, by
    rw [← map_pow]
    refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
    have : φ j ^ Nψ = MvPowerSeries.subst φ ((MvPowerSeries.X j : MvPowerSeries (Fin 2) B) ^ Nψ) := by
      rw [← MvPowerSeries.coe_substAlgHom hsub, map_pow, MvPowerSeries.coe_substAlgHom hsub, MvPowerSeries.subst_X hsub]
    rw [this]
    exact subst_mem_span_comp hφ0 (hNψ j)⟩
  let J : Ideal (MvPowerSeries (Fin 2) B ⧸ I) := Ideal.span (Set.range fun j => mk (φ j))
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range _)), Ideal.span_le]
    rintro _ ⟨j, rfl⟩; exact hφnil j
  obtain ⟨L, hL⟩ := hJ
  have hxJ : ∀ i, mk (MvPowerSeries.X i) ^ Nφ ∈ J := by
    intro i
    rw [← map_pow]
    have : (Ideal.span (Set.range φ)).map mk ≤ J := by
      rw [Ideal.map_span, Ideal.span_le]; rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩; exact Ideal.subset_span ⟨j, rfl⟩
    exact this (Ideal.mem_map_of_mem _ (hNφ i))
  refine ⟨Nφ * L, fun i => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, pow_mul]
  have h := Ideal.pow_mem_pow (hxJ i) L
  rw [hL, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

end KerDegComp

open KerDegComp in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {φ ψ : Series B} {d e : ℕ}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ d) (hψ : FormalODModule.HasKernelOfDegree ψ e) :
    FormalODModule.HasKernelOfDegree (ψ.comp φ) (d * e) := by
  classical
  set χ : Series B := ψ.comp φ with hχ
  have hχ0 : ∀ i, MvPowerSeries.constantCoeff (χ i) = 0 := Series.constantCoeff_comp hψ0 hφ0
  obtain ⟨Nφ, hNφ⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree φ hφ0 hφ
  obtain ⟨Nψ, hNψ⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree ψ hψ0 hψ
  obtain ⟨Nχ, hNχ⟩ := exists_X_pow_mem_comp hφ0 hNφ hNψ
  have hsubφ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0

  obtain ⟨hfinχ, hprojχ⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem χ hχ0 ⟨Nχ, hNχ⟩
  refine ⟨hfinχ, hprojχ, ?_⟩

  intro κ _ f
  have hφκ := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f φ hφ0 hφ
  have hψκ := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f ψ hψ0 hψ
  have hφκ0 : ∀ i, MvPowerSeries.constantCoeff ((φ.map f) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hφ0, map_zero]
  have hcomp := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field (RingHom.id κ) hψκ hφκ0 hφκ
  rw [Series.map_ringHom_id] at hcomp
  have h3 := hcomp.2.2 κ (RingHom.id κ)
  rw [Series.map_ringHom_id] at h3
  rw [show χ.map f = (ψ.map f).comp (φ.map f) from Series.map_comp f ψ φ hφ0, mul_comm d e]
  exact h3

end S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp (solution)
