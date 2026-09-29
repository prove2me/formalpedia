-- Prove2me | solution 1 for CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9a98100c-2ae9-5610-9e2f-b2fe6bdd6dce

import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Theorems.Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal
import Theorems.Thm_IharaLemma_isLocalizedModule_comap_primeCompl
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner

set_option autoImplicit false

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open scoped IsMulCommutative

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

private theorem exists_cornerRing_residue {Λ B k : Type} [CommRing Λ] [CommRing B] [Field k]
    [Algebra Λ B] (hπ : Function.Surjective (algebraMap Λ B)) (θ : Λ →+* k)
    (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    (hcomap : (S.𝔪 i).comap (algebraMap Λ B) = RingHom.ker θ) :
    ∃ r : S.CornerRing i →+* k, ∀ a : Λ, r (S.toCornerRing i (algebraMap Λ B a)) = θ a := by
  have hker : RingHom.ker (algebraMap Λ B) ≤ RingHom.ker θ := by
    intro a ha
    rw [← hcomap, Ideal.mem_comap, (RingHom.mem_ker).mp ha]
    exact (S.𝔪 i).zero_mem
  let r₀ : B →+* k := ((algebraMap Λ B).liftOfSurjective hπ) ⟨θ, hker⟩
  have hr₀ : ∀ a : Λ, r₀ (algebraMap Λ B a) = θ a := fun a =>
    RingHom.liftOfSurjective_comp_apply (f := algebraMap Λ B) hπ ⟨θ, hker⟩ a
  have hunit : ∀ y : (S.𝔪 i).primeCompl, IsUnit (r₀ y) := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := hπ y
    refine isUnit_iff_ne_zero.mpr fun h0 => hy ?_
    rw [hr₀] at h0
    have ha : a ∈ (S.𝔪 i).comap (algebraMap Λ B) := by
      rw [hcomap]; exact (RingHom.mem_ker).mpr h0
    exact (Ideal.mem_comap).mp ha
  refine ⟨IsLocalization.lift hunit, fun a => ?_⟩
  rw [show S.toCornerRing i (algebraMap Λ B a) = algebraMap B (S.CornerRing i) (algebraMap Λ B a) from
    Subtype.ext rfl, IsLocalization.lift_eq hunit, hr₀]

private theorem isLocalizedModule_toCorner_restrictScalars {Λ B : Type} [CommRing Λ] [CommRing B]
    [Algebra Λ B] (hπ : Function.Surjective (algebraMap Λ B))
    {V : Type} [AddCommGroup V] [Module B V] [Module Λ V] [IsScalarTower Λ B V]
    (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) (𝔭 : Ideal Λ) [𝔭.IsPrime]
    (hcomap : (S.𝔪 i).comap (algebraMap Λ B) = 𝔭) :
    IsLocalizedModule 𝔭.primeCompl ((IharaLemma.toCorner (M := V) (S.e i)).restrictScalars Λ) := by
  subst hcomap
  haveI := S.isLocalizedModule_toCorner_maximalIdeal i (M := V)
  exact IharaLemma.isLocalizedModule_comap_primeCompl (M := V)
    (N := ↥(IharaLemma.cornerSubmodule (M := V) (S.e i))) hπ (S.𝔪 i)
    (IharaLemma.toCorner (M := V) (S.e i))

private theorem linearEquiv_smul_eq_toCornerRing_smul {Λ B : Type} [CommRing Λ] [CommRing B]
    [Algebra Λ B] {V : Type} [AddCommGroup V] [Module B V] [Module Λ V] [IsScalarTower Λ B V]
    (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) {M : Type} [AddCommGroup M] [Module Λ M]
    (e : M ≃ₗ[Λ] ↥(IharaLemma.cornerSubmodule (M := V) (S.e i))) (a : Λ) (m : M) :
    e (a • m) = S.toCornerRing i (algebraMap Λ B a) • e m := by
  rw [map_smul]
  apply Subtype.ext
  rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, Submodule.coe_smul_of_tower]
  have hcoe : ((S.toCornerRing i (algebraMap Λ B a) : S.CornerRing i) : B)
      = S.e i * algebraMap Λ B a * S.e i := rfl
  rw [hcoe, mul_comm (S.e i) (algebraMap Λ B a), mul_assoc, (S.idem i).eq, mul_smul,
    S.e_smul_coe i (e m), algebraMap_smul B a ((e m : _) : V)]

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) :
    Module.Finite 𝒪 ↥D.opSubalgebra ∧
      (Subsingleton D.ML ∨
        ∃ (S : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i : Fin S.n)
          (r : S.CornerRing i →+* k),
          Function.Surjective r ∧
            (∀ c : 𝒪, r (algebraMap 𝒪 (S.CornerRing i) c) = algebraMap 𝒪 k c) ∧
            (∀ g : D.Gen,
              r (S.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩)
                = D.θbar g) ∧
            ∃ e : D.ML ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
              ∀ (g : D.Gen) (m : D.ML),
                e ((MvPolynomial.X g : D.FreeAlg) • m)
                  = S.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
                      • e m) := by
  classical

  let opB : D.Gen → ↥D.opSubalgebra := fun g =>
    ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  let ψ : D.FreeAlg →ₐ[𝒪] ↥D.opSubalgebra := MvPolynomial.aeval opB
  have hψX : ∀ g, ψ (MvPolynomial.X g) = opB g := fun g => MvPolynomial.aeval_X opB g
  have hψ_val : ∀ a : D.FreeAlg, ((ψ a : ↥D.opSubalgebra) : Module.End 𝒪 V) = D.opAlgHom a :=
    fun _ => rfl
  have hrange : D.opSubalgebra ≤ D.opAlgHom.range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨g, rfl⟩
    exact (AlgHom.mem_range _).mpr ⟨MvPolynomial.X g, D.opAlgHom_X g⟩
  have hψ_surj : Function.Surjective ψ := by
    intro b
    obtain ⟨a, ha⟩ := (AlgHom.mem_range _).mp (hrange b.2)
    exact ⟨a, Subtype.ext ((hψ_val a).trans ha)⟩
  have hψr_surj : Function.Surjective ψ.toRingHom := hψ_surj

  haveI hBfin : Module.Finite 𝒪 ↥D.opSubalgebra :=
    Module.Finite.of_injective D.opSubalgebra.val.toLinearMap Subtype.val_injective
  refine ⟨hBfin, ?_⟩

  letI : Algebra D.FreeAlg ↥D.opSubalgebra := ψ.toRingHom.toAlgebra
  have halg : ∀ a : D.FreeAlg, algebraMap D.FreeAlg ↥D.opSubalgebra a = ψ a := fun _ => rfl
  have hBsmul : ∀ (b : ↥D.opSubalgebra) (v : V), b • v = (b : Module.End 𝒪 V) v := fun _ _ => rfl
  have hΛsmul : ∀ (a : D.FreeAlg) (v : V), a • v = D.opAlgHom a v := fun _ _ => rfl
  haveI : IsScalarTower D.FreeAlg ↥D.opSubalgebra V :=
    ⟨fun a b v => by
      rw [Algebra.smul_def, halg, mul_smul, hBsmul (ψ a), hψ_val, hΛsmul]⟩
  haveI : IsScalarTower 𝒪 ↥D.opSubalgebra V :=
    ⟨fun c b v => by
      rw [hBsmul, hBsmul, Subalgebra.coe_smul, LinearMap.smul_apply]⟩

  have h𝔭 : D.mTheta.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective D.thetaTilde.toRingHom (thetaTilde_surjective hk D)
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective ψ.toRingHom hψ_surj h𝔭 with htop | hmax
  ·
    left
    have hsup : (1 : D.FreeAlg) ∈ D.mTheta ⊔ RingHom.ker ψ.toRingHom := by
      have h := Ideal.comap_map_of_surjective ψ.toRingHom hψ_surj D.mTheta
      rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot] at h
      rw [← h]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hsup
    obtain ⟨p, hp, s, hs, hps⟩ := hsup
    have hs𝔭 : s ∉ D.mTheta := fun h =>
      h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr (hps ▸ D.mTheta.add_mem hp h))
    have hs0 : ψ s = 0 := (RingHom.mem_ker).mp hs
    have hsV : ∀ v : V, s • v = 0 := fun v => by
      rw [hΛsmul, ← hψ_val, hs0, Subalgebra.coe_zero, LinearMap.zero_apply]
    exact subsingleton_localizedModule_of_smul_eq_zero D.mTheta.primeCompl (M := V) ⟨s, hs𝔭⟩ hsV
  ·
    right
    have hcomap : (D.mTheta.map ψ.toRingHom).comap (algebraMap D.FreeAlg ↥D.opSubalgebra)
        = D.mTheta := by
      have hne := Ideal.comap_ne_top ψ.toRingHom hmax.ne_top
      rw [Ideal.comap_map_of_surjective ψ.toRingHom hψr_surj, ← RingHom.ker_eq_comap_bot] at hne
      have halgr : algebraMap D.FreeAlg ↥D.opSubalgebra = ψ.toRingHom := RingHom.ext fun a => halg a
      rw [halgr, Ideal.comap_map_of_surjective ψ.toRingHom hψr_surj, ← RingHom.ker_eq_comap_bot]
      exact (h𝔭.eq_of_le hne le_sup_left).symm
    obtain ⟨S⟩ := IharaLemma.nonempty_idempotentSplitting_of_finite 𝒪 ↥D.opSubalgebra
    obtain ⟨i, hi⟩ := S.exists_eq _ hmax
    rw [← hi] at hcomap
    have hπ : Function.Surjective (algebraMap D.FreeAlg ↥D.opSubalgebra) := fun b => by
      obtain ⟨a, ha⟩ := hψ_surj b
      exact ⟨a, ha⟩

    obtain ⟨r, hr⟩ := exists_cornerRing_residue hπ D.thetaTilde.toRingHom S i hcomap

    haveI h₃ : IsLocalizedModule D.mTheta.primeCompl
        ((IharaLemma.toCorner (M := V) (S.e i)).restrictScalars D.FreeAlg) :=
      isLocalizedModule_toCorner_restrictScalars hπ (V := V) S i D.mTheta hcomap
    haveI : IsScalarTower 𝒪 D.FreeAlg ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)) :=
      ⟨fun c a x => Subtype.ext (smul_assoc c a (x : V))⟩
    let eΛ : D.ML ≃ₗ[D.FreeAlg] ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)) :=
      IsLocalizedModule.iso D.mTheta.primeCompl
        ((IharaLemma.toCorner (M := V) (S.e i)).restrictScalars D.FreeAlg)
    refine ⟨S, i, r, ?_, ?_, ?_, eΛ.restrictScalars 𝒪, ?_⟩
    ·
      intro c
      obtain ⟨a, ha⟩ := thetaTilde_surjective hk D c
      exact ⟨S.toCornerRing i (algebraMap D.FreeAlg ↥D.opSubalgebra a), (hr a).trans ha⟩
    ·
      intro c
      have h1 : algebraMap 𝒪 (S.CornerRing i) c = S.toCornerRing i (algebraMap 𝒪 ↥D.opSubalgebra c) :=
        rfl
      have h2 : algebraMap 𝒪 ↥D.opSubalgebra c
          = algebraMap D.FreeAlg ↥D.opSubalgebra (algebraMap 𝒪 D.FreeAlg c) := by
        rw [halg]; exact (ψ.commutes c).symm
      rw [h1, h2, hr]
      exact D.thetaTilde.commutes c
    ·
      intro g
      have hopB : (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)
          = opB g := rfl
      rw [hopB, ← hψX g, ← halg, hr]
      exact MvPolynomial.aeval_X D.θbar g
    ·
      intro g m
      have hopB : (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)
          = opB g := rfl
      rw [hopB, LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply, ← hψX g, ← halg]
      exact linearEquiv_smul_eq_toCornerRing_smul S i eΛ (MvPolynomial.X g) m

end S_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
end P2MW
export P2MW.S_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner (solution)
