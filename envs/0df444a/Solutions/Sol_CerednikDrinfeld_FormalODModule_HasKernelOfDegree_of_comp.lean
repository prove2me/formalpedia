-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.HasKernelOfDegree.of_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d0d72f10-6487-553f-833b-6793809a5a8e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace HKDCancel

variable {B B' : Type} [CommRing B] [CommRing B']

theorem map_constantCoeff_eq_zero (g : B →+* B') {φ : Series B} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    ∀ i, MvPowerSeries.constantCoeff ((φ.map g) i) = 0 := fun i => by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map g (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ0, map_zero]

theorem map_X_pow_mem (g : B →+* B') {φ : Series B} {N : ℕ}
    (hN : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ)) :
    ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B') ^ N ∈ Ideal.span (Set.range (φ.map g)) := fun i => by
  have h := Ideal.mem_map_of_mem (MvPowerSeries.map g : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B') (hN i)
  rw [map_pow, MvPowerSeries.map_X, Ideal.map_span] at h
  refine (Ideal.span_mono ?_) h
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩

theorem hasKernelOfDegree_finrank_of_field {κ : Type} [Field κ] (ψ : Series κ)
    (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ N ∈ Ideal.span (Set.range ψ)) :
    FormalODModule.HasKernelOfDegree ψ (Module.finrank κ (FormalODModule.KerAlgebra ψ)) := by
  obtain ⟨hfin, hproj⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem ψ hψ0 hN
  refine ⟨hfin, hproj, fun κ' _ g => ?_⟩
  letI : Algebra κ κ' := g.toAlgebra
  haveI := hfin
  haveI : Module.Free κ (FormalODModule.KerAlgebra ψ) := Module.Free.of_divisionRing κ _
  obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ') ψ hN
  have h1 : Module.finrank κ' (κ' ⊗[κ] FormalODModule.KerAlgebra ψ) = Module.finrank κ (FormalODModule.KerAlgebra ψ) :=
    Module.finrank_baseChange
  rw [← h1]
  exact (LinearEquiv.finrank_eq e.toLinearEquiv).symm

theorem nontrivial_kerAlgebra_of_field {κ : Type} [Field κ] (φ : Series κ)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) : Nontrivial (FormalODModule.KerAlgebra φ) := by
  have hle : Ideal.span (Set.range φ) ≤ RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) κ →+* κ) :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hφ0 i)
  have hne : Ideal.span (Set.range φ) ≠ ⊤ := fun h => by
    have : (1 : MvPowerSeries (Fin 2) κ) ∈ RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) κ →+* κ) :=
      hle (h.symm ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  refine ⟨⟨0, 1, fun h01 => hne ?_⟩⟩
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  have : (Ideal.Quotient.mk (Ideal.span (Set.range φ)) (1 : MvPowerSeries (Fin 2) κ)) = 1 := map_one _
  rw [this]
  exact h01.symm

end HKDCancel

open HKDCancel in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {φ ψ : Series B} {d e : ℕ}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ d) (hcomp : FormalODModule.HasKernelOfDegree (ψ.comp φ) (d * e)) :
    FormalODModule.HasKernelOfDegree ψ e := by
  classical
  have hc0 : ∀ i, MvPowerSeries.constantCoeff ((ψ.comp φ) i) = 0 := Series.constantCoeff_comp hψ0 hφ0
  obtain ⟨Nc, hNc⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree (ψ.comp φ) hc0 hcomp
  obtain ⟨Nψ, hNψ⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_X_pow_mem_span_comp hφ0 hψ0 hφ ⟨Nc, hNc⟩
  obtain ⟨hfin, hproj⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem ψ hψ0 ⟨Nψ, hNψ⟩
  refine ⟨hfin, hproj, fun κ _ f => ?_⟩

  have hφκ := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f φ hφ0 hφ
  have hcκ := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f (ψ.comp φ) hc0 hcomp
  rw [Series.map_comp f ψ φ hφ0] at hcκ
  have hψκ := hasKernelOfDegree_finrank_of_field (ψ.map f) (map_constantCoeff_eq_zero f hψ0) ⟨Nψ, map_X_pow_mem f hNψ⟩
  set a := Module.finrank κ (FormalODModule.KerAlgebra (ψ.map f)) with ha

  have hmul := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field (RingHom.id κ) hψκ
    (map_constantCoeff_eq_zero f hφ0) hφκ
  rw [Series.map_ringHom_id] at hmul
  have e1 := hmul.2.2 κ (RingHom.id κ)
  have e2 := hcκ.2.2 κ (RingHom.id κ)
  rw [e2] at e1

  have hd : 0 < d := by
    have e3 := hφκ.2.2 κ (RingHom.id κ)
    rw [Series.map_ringHom_id] at e3
    rw [← e3]
    haveI := nontrivial_kerAlgebra_of_field (φ.map f) (map_constantCoeff_eq_zero f hφ0)
    haveI : Module.Finite κ (FormalODModule.KerAlgebra (φ.map f)) := hφκ.1
    exact Module.finrank_pos

  have : e = a := by
    apply Nat.eq_of_mul_eq_mul_left hd
    rw [e1, mul_comm]
  rw [this]

end S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp (solution)
