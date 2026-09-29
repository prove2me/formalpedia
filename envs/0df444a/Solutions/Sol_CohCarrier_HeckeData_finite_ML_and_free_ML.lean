-- Prove2me | solution 1 for CohCarrier.HeckeData.finite_ML_and_free_ML
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c7eac964-a92f-529d-9929-6c91a2c2f9dd

import Definitions.Def_CohCarrier_HeckeData
import Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Theorems.Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal
import Theorems.Thm_IharaLemma_isLocalizedModule_comap_primeCompl
import Theorems.Thm_IharaLemma_finite_cornerSubmodule
import Theorems.Thm_IharaLemma_free_cornerSubmodule
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_finite_ML_and_free_ML

set_option autoImplicit false

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

private theorem thetaTilde_surjective {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V]
    [Module 𝒪 V] {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) : Function.Surjective D.thetaTilde := by
  intro c
  obtain ⟨r, hr⟩ := hk c
  exact ⟨algebraMap 𝒪 D.FreeAlg r, by rw [AlgHom.commutes]; exact hr⟩

private theorem subsingleton_localizedModule_of_smul_eq_zero {R : Type} [CommRing R]
    (S : Submonoid R) {M : Type} [AddCommGroup M] [Module R M] (s : S)
    (hs : ∀ m : M, (s : R) • m = 0) : Subsingleton (LocalizedModule S M) := by
  have h0 : ∀ x : LocalizedModule S M, x = 0 := fun x => by
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq]
      exact ⟨s, by simp [Submonoid.smul_def, hs]⟩
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

theorem solution {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) := by
  classical

  set I : Ideal D.FreeAlg := RingHom.ker D.opAlgHom.toRingHom with hI
  let φ : (D.FreeAlg ⧸ I) →ₐ[𝒪] Module.End 𝒪 V :=
    Ideal.Quotient.liftₐ I D.opAlgHom fun a ha => (RingHom.mem_ker).mp ha
  have hφ_inj : Function.Injective φ := fun x y hxy =>
    RingHom.lift_injective_of_ker_le_ideal I (f := D.opAlgHom.toRingHom)
      (fun a ha => (RingHom.mem_ker).mp ha) le_rfl hxy
  have hφ_mk : ∀ a : D.FreeAlg, φ (Ideal.Quotient.mk I a) = D.opAlgHom a := fun a =>
    Ideal.Quotient.lift_mk I _ _

  haveI : IsNoetherian 𝒪 (D.FreeAlg ⧸ I) := isNoetherian_of_injective φ.toLinearMap hφ_inj

  letI : Module (D.FreeAlg ⧸ I) V := Module.compHom V φ.toRingHom
  have hsmul : ∀ (b : D.FreeAlg ⧸ I) (v : V), b • v = φ b v := fun _ _ => rfl
  haveI : IsScalarTower D.FreeAlg (D.FreeAlg ⧸ I) V :=
    ⟨fun a b v => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hab : a • Ideal.Quotient.mk I b = Ideal.Quotient.mk I (a * b) := rfl
      rw [hab]
      simp only [hsmul]
      rw [hφ_mk, hφ_mk, map_mul, Module.End.mul_apply]
      rfl⟩
  haveI : IsScalarTower 𝒪 (D.FreeAlg ⧸ I) V :=
    ⟨fun r b v => by rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩

  have h𝔭 : D.mTheta.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective D.thetaTilde.toRingHom (thetaTilde_surjective hk D)
  have hmk : Function.Surjective (algebraMap D.FreeAlg (D.FreeAlg ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective h𝔭 with htop | hmax
  ·
    have hsup : (1 : D.FreeAlg) ∈ D.mTheta ⊔ I := by
      have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        D.mTheta
      rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
      rw [← h]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hsup
    obtain ⟨p, hp, s, hs, hps⟩ := hsup
    have hs𝔭 : s ∉ D.mTheta := fun h =>
      h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr (hps ▸ D.mTheta.add_mem hp h))
    have hsV : ∀ v : V, s • v = 0 := fun v => by
      show D.opAlgHom s v = 0
      rw [show D.opAlgHom s = 0 from (RingHom.mem_ker).mp hs]
      rfl
    haveI : Subsingleton D.ML :=
      subsingleton_localizedModule_of_smul_eq_zero D.mTheta.primeCompl (M := V) ⟨s, hs𝔭⟩ hsV
    haveI : Finite D.ML := Finite.of_subsingleton
    exact ⟨inferInstance, fun _ => inferInstance⟩
  ·
    have hcomap : (D.mTheta.map (Ideal.Quotient.mk I)).comap (algebraMap D.FreeAlg (D.FreeAlg ⧸ I))
        = D.mTheta := by
      have hne := Ideal.comap_ne_top (Ideal.Quotient.mk I) hmax.ne_top
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker] at hne
      rw [Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact (h𝔭.eq_of_le hne le_sup_left).symm
    obtain ⟨S⟩ := IharaLemma.nonempty_idempotentSplitting_of_finite 𝒪 (D.FreeAlg ⧸ I)
    obtain ⟨i, hi⟩ := S.exists_eq _ hmax
    rw [← hi] at hcomap

    haveI h₁ := S.isLocalizedModule_toCorner_maximalIdeal i (M := V)
    haveI h₂ := IharaLemma.isLocalizedModule_comap_primeCompl hmk (S.𝔪 i)
      (IharaLemma.toCorner (M := V) (S.e i))
    haveI h₃ : IsLocalizedModule D.mTheta.primeCompl
        ((IharaLemma.toCorner (M := V) (S.e i)).restrictScalars D.FreeAlg) := by
      convert h₂ using 3
      all_goals try rfl
      exact hcomap.symm
    haveI : IsScalarTower 𝒪 D.FreeAlg ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)) :=
      ⟨fun r a x => Subtype.ext (smul_assoc r a (x : V))⟩
    let e : D.ML ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)) :=
      (IsLocalizedModule.iso D.mTheta.primeCompl
        ((IharaLemma.toCorner (M := V) (S.e i)).restrictScalars D.FreeAlg)).restrictScalars 𝒪
    haveI := IharaLemma.finite_cornerSubmodule (𝒪 := 𝒪) (V := V) (S.e i)
    refine ⟨Module.Finite.equiv e.symm, fun hV => ?_⟩
    haveI := hV
    haveI := IharaLemma.free_cornerSubmodule (𝒪 := 𝒪) (V := V) (S.e i) (S.idem i)
    exact Module.Free.of_equiv e.symm

end S_CohCarrier_HeckeData_finite_ML_and_free_ML
end P2MW
export P2MW.S_CohCarrier_HeckeData_finite_ML_and_free_ML (solution)
