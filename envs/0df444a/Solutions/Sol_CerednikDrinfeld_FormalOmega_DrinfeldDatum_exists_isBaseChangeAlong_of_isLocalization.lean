-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bf519375-3002-5a35-98ab-dc63caea3133

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24BC

theorem isLocalization_atPrime_locRing {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (S : Submonoid B) [IsLocalization S C] (y : PrimeSpectrum C) :
    haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal :=
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S (locRing C y) y.asIdeal

def τB {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') : T →ₗ[B] T' :=
  { toFun := τ, map_add' := fun a b => map_add τ a b, map_smul' := fun b t => by
      rw [LinearMap.map_smulₛₗ]
      show algebraMap B C b • τ t = b • τ t
      exact algebraMap_smul C b (τ t) }

theorem τB_apply {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (t : T) : τB T T' τ t = τ t := rfl

theorem isBaseChange_τB {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (hτ : Submodule.span C (Set.range τ) = ⊤) :
    IsBaseChange C (τB T T' τ) := by
  have hsurj : Function.Surjective ((τB T T' τ).liftBaseChange C) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← hτ]
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) (fun t => by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul])

noncomputable def γ {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (y : PrimeSpectrum C) :
    T →ₗ[B] stalk C y T' :=
  ((LocalizedModule.mkLinearMap y.asIdeal.primeCompl T').restrictScalars B).comp (τB T T' τ)

theorem γ_apply {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (y : PrimeSpectrum C) (t : T) :
    γ T T' τ y t = LocalizedModule.mk (τ t) 1 := rfl

theorem isLocalizedModule_γ {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (S : Submonoid B) [IsLocalization S C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) :
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T T' τ y) := by
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B C (stalk C y T') := inferInstance
  haveI : IsScalarTower B (locRing C y) (stalk C y T') := inferInstance
  haveI : IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal :=
    isLocalization_atPrime_locRing (𝒪 := 𝒪) S y
  rw [isLocalizedModule_iff_isBaseChange (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (locRing C y)]
  exact IsBaseChange.comp (isBaseChange_τB T T' τ hτ)
    (IsLocalizedModule.isBaseChange y.asIdeal.primeCompl (locRing C y) (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T'))

end B24BC

namespace B24BC

theorem iso_γ_mk {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (S : Submonoid B) [IsLocalization S C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) (t : T) (s : B)
    (hs : s ∈ (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl) :
    haveI := isLocalizedModule_γ S T T' τ hτ y
    IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T T' τ y)
        (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk (τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) := by
  haveI := isLocalizedModule_γ S T T' τ hτ y
  apply ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (γ T T' τ y) ⟨s, hs⟩)).1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_smul, LocalizedModule.smul'_mk,
    ← algebraMap_smul C s (LocalizedModule.mk (τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl)),
    LocalizedModule.smul'_mk]
  have h1 : LocalizedModule.mk (s • t) (⟨s, hs⟩ : (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl) =
      LocalizedModule.mk t 1 := LocalizedModule.mk_cancel ⟨s, hs⟩ t
  have h2 : LocalizedModule.mk (algebraMap B C s • τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) =
      LocalizedModule.mk (τ t) 1 := LocalizedModule.mk_cancel (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) (τ t)
  rw [h1, h2, IsLocalizedModule.iso_mk_one, γ_apply]

end B24BC

namespace B24BC

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

noncomputable def ιB (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (N : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B N →ₗ[B] latticeBaseChange 𝒪 K A N :=
  { toFun := LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap
    map_add' := fun a b => map_add _ a b
    map_smul' := fun b p => by
      rw [rTensor_smul_left (IsScalarTower.toAlgHom 𝒪 B A) N b p, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rfl }

theorem ιB_apply (N : FullLattice 𝒪 K) (p : latticeBaseChange 𝒪 K B N) :
    ιB A N p = LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap p := rfl

theorem ιB_one_tmul (N : FullLattice 𝒪 K) (v : ↥N.1) : ιB A N ((1 : B) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] v :=
  rTensor_one_tmul _ N v

theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K) :
    IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

theorem ιB_mem_lineBaseChange_iff (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K)
    (D : Submodule B (latticeBaseChange 𝒪 K B N)) (p : latticeBaseChange 𝒪 K B N) :
    ιB A N p ∈ lineBaseChange (IsScalarTower.toAlgHom 𝒪 B A) N D ↔ ∃ s ∈ S, s • p ∈ D := by
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := A) S N
  have hspan : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B A) N D = D.localized' A S (ιB A N) := by
    rw [Submodule.localized'_eq_span]; rfl
  rw [hspan, Submodule.mem_localized']
  constructor
  · rintro ⟨m, hm, s, hms⟩
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hms
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S (ιB A N)).mp hms
    refine ⟨c * s, mul_mem c.2 s.2, ?_⟩
    rw [mul_smul]
    have hc' : (c : B) • ((s : B) • p) = (c : B) • m := by
      rw [← Submonoid.smul_def, ← Submonoid.smul_def c m, hc]
    rw [hc']
    exact D.smul_mem _ hm
  · rintro ⟨s, hs, hsp⟩
    exact ⟨s • p, hsp, ⟨s, hs⟩, by rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, map_smul]⟩

end Loc

end B24BC

namespace B24BC

theorem map_mk {R : Type} [CommRing R] (S : Submonoid R) {M N : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (m : M) (s : S) :
    LocalizedModule.map S g (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s :=
  IsLocalizedModule.map_LocalizedModules S g m s

theorem iso_γ_natural {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (S : Submonoid B) [IsLocalization S C]
    (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀]
    (T₀' : Type) [AddCommGroup T₀'] [Module C T₀'] [Module.Invertible C T₀'] [Module B T₀'] [IsScalarTower B C T₀']
    (τ₀ : T₀ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T₀')
    (hτ₀ : Submodule.span C (Set.range τ₀) = ⊤)
    (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁]
    (T₁' : Type) [AddCommGroup T₁'] [Module C T₁'] [Module.Invertible C T₁'] [Module B T₁'] [IsScalarTower B C T₁']
    (τ₁ : T₁ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T₁')
    (hτ₁ : Submodule.span C (Set.range τ₁) = ⊤)
    (y : PrimeSpectrum C) (P : T₀ →ₗ[B] T₁) (P' : T₀' →ₗ[C] T₁') (hP : ∀ t, τ₁ (P t) = P' (τ₀ t))
    (m : stalk B (PrimeSpectrum.comap (algebraMap B C) y) T₀) :
    haveI := isLocalizedModule_γ S T₀ T₀' τ₀ hτ₀ y
    haveI := isLocalizedModule_γ S T₁ T₁' τ₁ hτ₁ y
    IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T₁ T₁' τ₁ y)
        (LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl P m) =
      LocalizedModule.map y.asIdeal.primeCompl P'
        (IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T₀ T₀' τ₀ y) m) := by
  haveI := isLocalizedModule_γ S T₀ T₀' τ₀ hτ₀ y
  haveI := isLocalizedModule_γ S T₁ T₁' τ₁ hτ₁ y
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [map_mk, iso_γ_mk S T₁ T₁' τ₁ hτ₁ y (P t) s s.2, iso_γ_mk S T₀ T₀' τ₀ hτ₀ y t s s.2, map_mk, hP]

end B24BC

namespace B24BC
section Construction

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]

noncomputable def τbc (T : Type) [AddCommGroup T] [Module B T] :
    T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] C ⊗[B] T :=
  { toFun := fun t => (1 : C) ⊗ₜ[B] t
    map_add' := fun a b => TensorProduct.tmul_add _ a b
    map_smul' := fun b t => by
      show (1 : C) ⊗ₜ[B] (b • t) = (algebraMap B C b) • ((1 : C) ⊗ₜ[B] t)
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, algebraMap_smul] }

theorem τbc_apply (T : Type) [AddCommGroup T] [Module B T] (t : T) :
    τbc (𝒪 := 𝒪) (B := B) (C := C) T t = (1 : C) ⊗ₜ[B] t := rfl

theorem span_range_τbc (T : Type) [AddCommGroup T] [Module B T] :
    Submodule.span C (Set.range (τbc (𝒪 := 𝒪) (B := B) (C := C) T)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul c t =>
    have : c ⊗ₜ[B] t = c • ((1 : C) ⊗ₜ[B] t) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem baseChange_comp_apply {T₀ T₁ : Type} [AddCommGroup T₀] [Module B T₀] [AddCommGroup T₁] [Module B T₁]
    (P₀ : T₀ →ₗ[B] T₁) (P₁ : T₁ →ₗ[B] T₀) (h : ∀ t, P₁ (P₀ t) = algebraMap 𝒪 B π • t) (z : C ⊗[B] T₀) :
    (P₁.baseChange C) ((P₀.baseChange C) z) = algebraMap 𝒪 C π • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add a b ha hb => simp only [map_add, smul_add, ha, hb]
  | tmul c t =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h, TensorProduct.tmul_smul,
      IsScalarTower.algebraMap_apply 𝒪 B C, algebraMap_smul C (algebraMap 𝒪 B π) (c ⊗ₜ[B] t)]

end Construction
end B24BC

namespace B24BC
section Q
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B) (x' : PrimeSpectrum C)

noncomputable def β₀Q : stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₀ ≃ₗ[B] stalk C x' (C ⊗[B] Q.T₀) :=
  haveI := isLocalizedModule_γ (𝒪 := 𝒪) S Q.T₀ (C ⊗[B] Q.T₀) (τbc (𝒪 := 𝒪) Q.T₀) (span_range_τbc Q.T₀) x'
  IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl (γ (𝒪 := 𝒪) Q.T₀ (C ⊗[B] Q.T₀) (τbc (𝒪 := 𝒪) Q.T₀) x')

theorem β₀Q_mk (t : Q.T₀) (s : B) (hs : s ∈ (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl) :
    β₀Q (𝒪 := 𝒪) S Q x' (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk ((1 : C) ⊗ₜ[B] t) (⟨algebraMap B C s, hs⟩ : x'.asIdeal.primeCompl) :=
  iso_γ_mk S Q.T₀ (C ⊗[B] Q.T₀) (τbc Q.T₀) (span_range_τbc Q.T₀) x' t s hs

noncomputable def g₀Q : ↥(Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x')) →ₗ[𝒪] stalk C x' (C ⊗[B] Q.T₀) :=
  { toFun := fun v => β₀Q (𝒪 := 𝒪) S Q x' (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v))
    map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add, map_add]
    map_smul' := fun r v => by
      show β₀Q (𝒪 := 𝒪) S Q x' (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] (r • v))) =
        r • β₀Q (𝒪 := 𝒪) S Q x' (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v))
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) r ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v), map_smul,
        IsScalarTower.algebraMap_apply 𝒪 B (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) r, algebraMap_smul, map_smul]
      exact algebraMap_smul B r _ }

noncomputable def u₀Q : latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) →ₗ[locRing C x'] stalk C x' (C ⊗[B] Q.T₀) :=
  (g₀Q S Q x').liftBaseChange (locRing C x')

theorem u₀Q_tmul (a : locRing C x') (v : ↥(Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x'))) :
    u₀Q (𝒪 := 𝒪) S Q x' (a ⊗ₜ[𝒪] v) = a • β₀Q (𝒪 := 𝒪) S Q x' (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

noncomputable def β₁Q : stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₁ ≃ₗ[B] stalk C x' (C ⊗[B] Q.T₁) :=
  haveI := isLocalizedModule_γ (𝒪 := 𝒪) S Q.T₁ (C ⊗[B] Q.T₁) (τbc (𝒪 := 𝒪) Q.T₁) (span_range_τbc Q.T₁) x'
  IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl (γ (𝒪 := 𝒪) Q.T₁ (C ⊗[B] Q.T₁) (τbc (𝒪 := 𝒪) Q.T₁) x')

theorem β₁Q_mk (t : Q.T₁) (s : B) (hs : s ∈ (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl) :
    β₁Q (𝒪 := 𝒪) S Q x' (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk ((1 : C) ⊗ₜ[B] t) (⟨algebraMap B C s, hs⟩ : x'.asIdeal.primeCompl) :=
  iso_γ_mk S Q.T₁ (C ⊗[B] Q.T₁) (τbc Q.T₁) (span_range_τbc Q.T₁) x' t s hs

noncomputable def g₁Q : ↥(Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x')) →ₗ[𝒪] stalk C x' (C ⊗[B] Q.T₁) :=
  { toFun := fun v => β₁Q (𝒪 := 𝒪) S Q x' (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v))
    map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add, map_add]
    map_smul' := fun r v => by
      show β₁Q (𝒪 := 𝒪) S Q x' (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] (r • v))) =
        r • β₁Q (𝒪 := 𝒪) S Q x' (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v))
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) r ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v), map_smul,
        IsScalarTower.algebraMap_apply 𝒪 B (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) r, algebraMap_smul, map_smul]
      exact algebraMap_smul B r _ }

noncomputable def u₁Q : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) →ₗ[locRing C x'] stalk C x' (C ⊗[B] Q.T₁) :=
  (g₁Q S Q x').liftBaseChange (locRing C x')

theorem u₁Q_tmul (a : locRing C x') (v : ↥(Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x'))) :
    u₁Q (𝒪 := 𝒪) S Q x' (a ⊗ₜ[𝒪] v) = a • β₁Q (𝒪 := 𝒪) S Q x' (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

end Q
end B24BC

namespace B24BC
section Q2
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B) (x' : PrimeSpectrum C)

theorem β_map_Pi₀ (m : stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₀) :
    β₁Q (𝒪 := 𝒪) S Q x' (LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₀ m) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₀.baseChange C) (β₀Q (𝒪 := 𝒪) S Q x' m) :=
  iso_γ_natural S Q.T₀ (C ⊗[B] Q.T₀) (τbc Q.T₀) (span_range_τbc Q.T₀)
    Q.T₁ (C ⊗[B] Q.T₁) (τbc Q.T₁) (span_range_τbc Q.T₁) x' Q.Pi₀ (Q.Pi₀.baseChange C)
    (fun t => (LinearMap.baseChange_tmul _ _ _).symm) m

theorem β_map_Pi₁ (m : stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₁) :
    β₀Q (𝒪 := 𝒪) S Q x' (LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₁ m) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₁.baseChange C) (β₁Q (𝒪 := 𝒪) S Q x' m) :=
  iso_γ_natural S Q.T₁ (C ⊗[B] Q.T₁) (τbc Q.T₁) (span_range_τbc Q.T₁)
    Q.T₀ (C ⊗[B] Q.T₀) (τbc Q.T₀) (span_range_τbc Q.T₀) x' Q.Pi₁ (Q.Pi₁.baseChange C)
    (fun t => (LinearMap.baseChange_tmul _ _ _).symm) m

theorem u₀Q_ιB (p₀ : latticeBaseChange 𝒪 K B (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) :
    u₀Q (𝒪 := 𝒪) S Q x' (ιB (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) p₀) =
      β₀Q (𝒪 := 𝒪) S Q x' (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) p₀)) := by
  induction p₀ using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) = b • ((1 : B) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have l1 : ιB (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) (b ⊗ₜ[𝒪] v) = b • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    have l2 : ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) (b ⊗ₜ[𝒪] v) = b • ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    rw [l1, l2, LinearMap.map_smul_of_tower (u₀Q S Q x'), LinearMap.map_smul_of_tower (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x')), map_smul,
      u₀Q_tmul, one_smul]

theorem u₀Q_surjective : Function.Surjective (u₀Q (𝒪 := 𝒪) S Q x') := by
  haveI : IsScalarTower B C (locRing C x') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro m'
  obtain ⟨m, rfl⟩ := (β₀Q (𝒪 := 𝒪) S Q x').surjective m'
  obtain ⟨p, rfl⟩ := Q.u₀_surjective (PrimeSpectrum.comap (algebraMap B C) x') m
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))
  obtain ⟨⟨p₀, s⟩, hsp⟩ := IsLocalizedModule.surj (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) p
  have hunit : IsUnit (algebraMap B (locRing C x') s) := by
    rw [IsScalarTower.algebraMap_apply B C (locRing C x')]
    exact IsLocalization.map_units (locRing C x') (⟨algebraMap B C s, s.2⟩ : x'.asIdeal.primeCompl)
  refine ⟨((hunit.unit⁻¹ : (locRing C x')ˣ) : locRing C x') • ιB (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) p₀, ?_⟩
  rw [map_smul, u₀Q_ιB, ← hsp, Submonoid.smul_def, LinearMap.map_smul_of_tower, map_smul,
    ← algebraMap_smul (locRing C x') (s : B), smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]

theorem u₀Q_continuous (v : Fin 2 → K) (hv : v ∈ Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x')) :
    ∃ (c : C) (t' : C ⊗[B] Q.T₀), c ∉ x'.asIdeal ∧ ∀ (y' : PrimeSpectrum C) (hy : c ∉ y'.asIdeal),
      ∃ hvy : v ∈ Q.N₀ (PrimeSpectrum.comap (algebraMap B C) y'),
        u₀Q (𝒪 := 𝒪) S Q y' ((1 : locRing C y') ⊗ₜ[𝒪] (⟨v, hvy⟩ : ↥(Q.N₀ (PrimeSpectrum.comap (algebraMap B C) y')))) =
          LocalizedModule.mk t' ⟨c, hy⟩ := by
  obtain ⟨b, t, hb, H⟩ := Q.u₀_continuous (PrimeSpectrum.comap (algebraMap B C) x') v hv
  refine ⟨algebraMap B C b, (1 : C) ⊗ₜ[B] t, hb, fun y' hy' => ?_⟩
  obtain ⟨hvy, Hy⟩ := H (PrimeSpectrum.comap (algebraMap B C) y') hy'
  refine ⟨hvy, ?_⟩
  rw [u₀Q_tmul, one_smul, Hy]
  exact β₀Q_mk S Q y' t b hy'

theorem u₁Q_ιB (p₀ : latticeBaseChange 𝒪 K B (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))) :
    u₁Q (𝒪 := 𝒪) S Q x' (ιB (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) p₀) =
      β₁Q (𝒪 := 𝒪) S Q x' (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) p₀)) := by
  induction p₀ using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))) = b • ((1 : B) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have l1 : ιB (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) (b ⊗ₜ[𝒪] v) = b • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    have l2 : ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) (b ⊗ₜ[𝒪] v) = b • ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    rw [l1, l2, LinearMap.map_smul_of_tower (u₁Q S Q x'), LinearMap.map_smul_of_tower (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x')), map_smul,
      u₁Q_tmul, one_smul]

theorem u₁Q_surjective : Function.Surjective (u₁Q (𝒪 := 𝒪) S Q x') := by
  haveI : IsScalarTower B C (locRing C x') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro m'
  obtain ⟨m, rfl⟩ := (β₁Q (𝒪 := 𝒪) S Q x').surjective m'
  obtain ⟨p, rfl⟩ := Q.u₁_surjective (PrimeSpectrum.comap (algebraMap B C) x') m
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))
  obtain ⟨⟨p₀, s⟩, hsp⟩ := IsLocalizedModule.surj (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))) p
  have hunit : IsUnit (algebraMap B (locRing C x') s) := by
    rw [IsScalarTower.algebraMap_apply B C (locRing C x')]
    exact IsLocalization.map_units (locRing C x') (⟨algebraMap B C s, s.2⟩ : x'.asIdeal.primeCompl)
  refine ⟨((hunit.unit⁻¹ : (locRing C x')ˣ) : locRing C x') • ιB (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) p₀, ?_⟩
  rw [map_smul, u₁Q_ιB, ← hsp, Submonoid.smul_def, LinearMap.map_smul_of_tower, map_smul,
    ← algebraMap_smul (locRing C x') (s : B), smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]

theorem u₁Q_continuous (v : Fin 2 → K) (hv : v ∈ Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x')) :
    ∃ (c : C) (t' : C ⊗[B] Q.T₁), c ∉ x'.asIdeal ∧ ∀ (y' : PrimeSpectrum C) (hy : c ∉ y'.asIdeal),
      ∃ hvy : v ∈ Q.N₁ (PrimeSpectrum.comap (algebraMap B C) y'),
        u₁Q (𝒪 := 𝒪) S Q y' ((1 : locRing C y') ⊗ₜ[𝒪] (⟨v, hvy⟩ : ↥(Q.N₁ (PrimeSpectrum.comap (algebraMap B C) y')))) =
          LocalizedModule.mk t' ⟨c, hy⟩ := by
  obtain ⟨b, t, hb, H⟩ := Q.u₁_continuous (PrimeSpectrum.comap (algebraMap B C) x') v hv
  refine ⟨algebraMap B C b, (1 : C) ⊗ₜ[B] t, hb, fun y' hy' => ?_⟩
  obtain ⟨hvy, Hy⟩ := H (PrimeSpectrum.comap (algebraMap B C) y') hy'
  refine ⟨hvy, ?_⟩
  rw [u₁Q_tmul, one_smul, Hy]
  exact β₁Q_mk S Q y' t b hy'

end Q2
end B24BC

namespace B24BC
section Q3
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B) (x' : PrimeSpectrum C)

theorem u₁Q_incl (w : latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) :
    u₁Q (𝒪 := 𝒪) S Q x' (inclBaseChange (locRing C x') (M' := Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x')) (M := Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) (Q.le (PrimeSpectrum.comap (algebraMap B C) x')) w) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₀.baseChange C) (u₀Q (𝒪 := 𝒪) S Q x' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) = a • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [show inclBaseChange (locRing C x') (Q.le (PrimeSpectrum.comap (algebraMap B C) x')) ((1 : locRing C x') ⊗ₜ[𝒪] v) =
        ((1 : locRing C x') ⊗ₜ[𝒪] Submodule.inclusion (Q.le (PrimeSpectrum.comap (algebraMap B C) x')) v : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')))
        from LinearMap.baseChange_tmul _ _ _,
      u₁Q_tmul, u₀Q_tmul, one_smul, one_smul,
      show ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] Submodule.inclusion (Q.le (PrimeSpectrum.comap (algebraMap B C) x')) v : latticeBaseChange 𝒪 K (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))) =
        inclBaseChange (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.le (PrimeSpectrum.comap (algebraMap B C) x')) ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) from (LinearMap.baseChange_tmul _ _ _).symm,
      Q.u₁_incl, β_map_Pi₀]

theorem u₀Q_smul (w : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))) :
    u₀Q (𝒪 := 𝒪) S Q x' (((smulInto π (Q.smul_le (PrimeSpectrum.comap (algebraMap B C) x'))).baseChange (locRing C x') :
        latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x')) →ₗ[locRing C x'] latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) w) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₁.baseChange C) (u₁Q (𝒪 := 𝒪) S Q x' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (PrimeSpectrum.comap (algebraMap B C) x'))) = a • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [LinearMap.baseChange_tmul, u₀Q_tmul, u₁Q_tmul, one_smul, one_smul,
      show ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] smulInto π (Q.smul_le (PrimeSpectrum.comap (algebraMap B C) x')) v : latticeBaseChange 𝒪 K (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) (Q.L₀ (PrimeSpectrum.comap (algebraMap B C) x'))) =
        (smulInto π (Q.smul_le (PrimeSpectrum.comap (algebraMap B C) x'))).baseChange (locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) from
        (LinearMap.baseChange_tmul _ _ _).symm,
      Q.u₀_smul, β_map_Pi₁]

end Q3

section Strata

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]

theorem range_baseChange_le_iff {T₀ T₁ : Type} [AddCommGroup T₀] [Module B T₀] [AddCommGroup T₁] [Module B T₁]
    [Module.Invertible B T₁] (P : T₀ →ₗ[B] T₁) (x' : PrimeSpectrum C) :
    LinearMap.range (P.baseChange C) ≤ x'.asIdeal • (⊤ : Submodule C (C ⊗[B] T₁)) ↔
      LinearMap.range P ≤ (PrimeSpectrum.comap (algebraMap B C) x').asIdeal • (⊤ : Submodule B T₁) := by
  constructor
  · intro h
    rintro _ ⟨t, rfl⟩
    by_contra hnot
    obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem (PrimeSpectrum.comap (algebraMap B C) x').asIdeal (P t) hnot
    let ψ : C ⊗[B] T₁ →ₗ[C] C := (TensorProduct.AlgebraTensorModule.rid B C C).toLinearMap ∘ₗ φ.baseChange C
    have hψ : ψ ((1 : C) ⊗ₜ[B] P t) = algebraMap B C (φ (P t)) := by
      simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
    have key : ∀ z ∈ (x'.asIdeal • ⊤ : Submodule C (C ⊗[B] T₁)), ψ z ∈ x'.asIdeal := by
      intro z hz
      refine Submodule.smul_induction_on (p := fun z => ψ z ∈ x'.asIdeal) hz (fun r hr n _ => ?_) (fun a b ha hb => ?_)
      · show ψ (r • n) ∈ _
        rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ hr
      · show ψ (a + b) ∈ _
        rw [map_add]; exact Ideal.add_mem _ ha hb
    have hmem : (P.baseChange C) ((1 : C) ⊗ₜ[B] t) ∈ (x'.asIdeal • ⊤ : Submodule C (C ⊗[B] T₁)) := h ⟨_, rfl⟩
    rw [LinearMap.baseChange_tmul] at hmem
    have := key _ hmem
    rw [hψ] at this
    exact hφ this
  · intro h
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul c t =>
      rw [LinearMap.baseChange_tmul]
      refine Submodule.smul_induction_on (p := fun n => c ⊗ₜ[B] n ∈ (x'.asIdeal • ⊤ : Submodule C (C ⊗[B] T₁)))
        (h ⟨t, rfl⟩) (fun b hb n _ => ?_) (fun a b ha hb => ?_)
      · show c ⊗ₜ[B] (b • n) ∈ _
        rw [TensorProduct.tmul_smul, ← algebraMap_smul C b (c ⊗ₜ[B] n)]
        exact Submodule.smul_mem_smul hb Submodule.mem_top
      · show c ⊗ₜ[B] (a + b) ∈ _
        rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb

theorem smul_top_restrictScalars_le (S : Submonoid B) [IsLocalization S C] (x' : PrimeSpectrum C)
    (M : Type) [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] (m : M)
    (hm : m ∈ (x'.asIdeal • ⊤ : Submodule C M)) :
    m ∈ ((PrimeSpectrum.comap (algebraMap B C) x').asIdeal • ⊤ : Submodule B M) := by
  refine Submodule.smul_induction_on (p := fun m => m ∈ ((PrimeSpectrum.comap (algebraMap B C) x').asIdeal • ⊤ :
    Submodule B M)) hm (fun c hc n _ => ?_) (fun a b ha hb => Submodule.add_mem _ ha hb)
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj S c

  have hb : b ∈ (PrimeSpectrum.comap (algebraMap B C) x').asIdeal := by
    show algebraMap B C b ∈ x'.asIdeal
    rw [← hbs]; exact Ideal.mul_mem_right _ _ hc
  have hunit : IsUnit (algebraMap B C s) := IsLocalization.map_units C s
  have : c • n = b • (((hunit.unit⁻¹ : Cˣ) : C) • n) := by
    rw [← algebraMap_smul C b, smul_smul, ← hbs, mul_assoc, Units.mul_inv_eq_one.mpr hunit.unit_spec.symm, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul hb Submodule.mem_top

end Strata
end B24BC

namespace B24BC
section Q4
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B) (x' : PrimeSpectrum C)

theorem inj₀Q (v : ↥(Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x')))
    (h : u₀Q (𝒪 := 𝒪) S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₁.baseChange C))).restrictScalars C ⊔
        x'.asIdeal • (⊤ : Submodule C (stalk C x' (C ⊗[B] Q.T₀)))) :
    Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₁)).restrictScalars B ⊔
        (PrimeSpectrum.comap (algebraMap B C) x').asIdeal • (⊤ : Submodule B (stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₀)) := by
  rw [u₀Q_tmul, one_smul] at h
  obtain ⟨r', hr', z', hz', hsum⟩ := Submodule.mem_sup.mp h
  rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr'
  obtain ⟨a', rfl⟩ := hr'
  obtain ⟨a, rfl⟩ := (β₁Q (𝒪 := 𝒪) S Q x').surjective a'
  rw [← β_map_Pi₁] at hsum
  have hz : z' = β₀Q (𝒪 := 𝒪) S Q x'
      (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) - LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₁ a) := by
    rw [map_sub, ← hsum, add_sub_cancel_left]
  have hzB := smul_top_restrictScalars_le S x' _ z' hz'
  rw [hz] at hzB
  have hn : Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) - LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₁ a ∈
      ((PrimeSpectrum.comap (algebraMap B C) x').asIdeal • ⊤ : Submodule B (stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₀)) := by
    have h2 := Submodule.mem_map_of_mem (f := (β₀Q (𝒪 := 𝒪) S Q x').symm.toLinearMap) hzB
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at h2
    exact h2
  have hdecomp : Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) =
      LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₁ a +
        (Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) - LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₁ a) := by
    rw [add_sub_cancel]
  rw [hdecomp]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right hn)

theorem inj₁Q (v : ↥(Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x')))
    (h : u₁Q (𝒪 := 𝒪) S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₀.baseChange C))).restrictScalars C ⊔
        x'.asIdeal • (⊤ : Submodule C (stalk C x' (C ⊗[B] Q.T₁)))) :
    Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₀)).restrictScalars B ⊔
        (PrimeSpectrum.comap (algebraMap B C) x').asIdeal • (⊤ : Submodule B (stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₁)) := by
  rw [u₁Q_tmul, one_smul] at h
  obtain ⟨r', hr', z', hz', hsum⟩ := Submodule.mem_sup.mp h
  rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr'
  obtain ⟨a', rfl⟩ := hr'
  obtain ⟨a, rfl⟩ := (β₀Q (𝒪 := 𝒪) S Q x').surjective a'
  rw [← β_map_Pi₀] at hsum
  have hz : z' = β₁Q (𝒪 := 𝒪) S Q x'
      (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) - LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₀ a) := by
    rw [map_sub, ← hsum, add_sub_cancel_left]
  have hzB := smul_top_restrictScalars_le S x' _ z' hz'
  rw [hz] at hzB
  have hn : Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) - LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₀ a ∈
      ((PrimeSpectrum.comap (algebraMap B C) x').asIdeal • ⊤ : Submodule B (stalk B (PrimeSpectrum.comap (algebraMap B C) x') Q.T₁)) := by
    have h2 := Submodule.mem_map_of_mem (f := (β₁Q (𝒪 := 𝒪) S Q x').symm.toLinearMap) hzB
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at h2
    exact h2
  have hdecomp : Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) =
      LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₀ a +
        (Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] v) - LocalizedModule.map (PrimeSpectrum.comap (algebraMap B C) x').asIdeal.primeCompl Q.Pi₀ a) := by
    rw [add_sub_cancel]
  rw [hdecomp]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right hn)

end Q4
end B24BC

namespace B24BC
section Datum
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B)

noncomputable def bcDatum : DrinfeldDatum (K := K) π C :=
  {
    N₀ := fun x' => Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x')
    N₁ := fun x' => Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x')
    full₀ := fun x' => Q.full₀ _
    full₁ := fun x' => Q.full₁ _
    le := fun x' => Q.le _
    smul_le := fun x' => Q.smul_le _
    isOpen_setOf_mem₀ := fun v => (Q.isOpen_setOf_mem₀ v).preimage (PrimeSpectrum.continuous_comap (algebraMap B C))
    isOpen_setOf_mem₁ := fun v => (Q.isOpen_setOf_mem₁ v).preimage (PrimeSpectrum.continuous_comap (algebraMap B C))
    T₀ := C ⊗[B] Q.T₀
    T₁ := C ⊗[B] Q.T₁
    invertible₀ := inferInstance
    invertible₁ := inferInstance
    Pi₀ := Q.Pi₀.baseChange C
    Pi₁ := Q.Pi₁.baseChange C
    Pi₁_Pi₀ := baseChange_comp_apply Q.Pi₀ Q.Pi₁ Q.Pi₁_Pi₀
    Pi₀_Pi₁ := baseChange_comp_apply Q.Pi₁ Q.Pi₀ Q.Pi₀_Pi₁
    u₀ := fun x' => u₀Q S Q x'
    u₁ := fun x' => u₁Q S Q x'
    u₁_incl := fun x' w => u₁Q_incl S Q x' w
    u₀_smul := fun x' w => u₀Q_smul S Q x' w
    u₀_surjective := fun x' => u₀Q_surjective S Q x'
    u₁_surjective := fun x' => u₁Q_surjective S Q x'
    u₀_continuous := fun x' v hv => u₀Q_continuous S Q x' v hv
    u₁_continuous := fun x' v hv => u₁Q_continuous S Q x' v hv
    locallyConstant₀ := fun x' h => by
      obtain ⟨U, hU, hxU, HU⟩ := Q.locallyConstant₀ _ ((range_baseChange_le_iff Q.Pi₀ x').mp h)
      exact ⟨_, hU.preimage (PrimeSpectrum.continuous_comap (algebraMap B C)), hxU,
        fun y' hy' hy's => HU _ hy' ((range_baseChange_le_iff Q.Pi₀ y').mp hy's)⟩
    locallyConstant₁ := fun x' h => by
      obtain ⟨U, hU, hxU, HU⟩ := Q.locallyConstant₁ _ ((range_baseChange_le_iff Q.Pi₁ x').mp h)
      exact ⟨_, hU.preimage (PrimeSpectrum.continuous_comap (algebraMap B C)), hxU,
        fun y' hy' hy's => HU _ hy' ((range_baseChange_le_iff Q.Pi₁ y').mp hy's)⟩
    injective₀ := fun x' v h => Q.injective₀ _ v (inj₀Q S Q x' v h)
    injective₁ := fun x' v h => Q.injective₁ _ v (inj₁Q S Q x' v h)
    hasDetIndex₀ := fun x' h => Q.hasDetIndex₀ _ ((range_baseChange_le_iff Q.Pi₀ x').mp h)
    hasDetIndex₁ := fun x' h => Q.hasDetIndex₁ _ ((range_baseChange_le_iff Q.Pi₁ x').mp h) }

theorem bcDatum_u₀ (x' : PrimeSpectrum C) : (bcDatum S Q).u₀ x' = u₀Q S Q x' := rfl
theorem bcDatum_u₁ (x' : PrimeSpectrum C) : (bcDatum S Q).u₁ x' = u₁Q S Q x' := rfl

end Datum
end B24BC

open B24BC in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (Q : DrinfeldDatum (K := K) π B) (S : Submonoid B)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization S C] :
    ∃ Q' : DrinfeldDatum (K := K) π C, Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B C) Q' := by
  classical
  refine ⟨bcDatum S Q, ⟨{
      N₀_eq := fun x' => rfl
      N₁_eq := fun x' => rfl
      τ₀ := τbc Q.T₀
      τ₁ := τbc Q.T₁
      span_range_τ₀ := span_range_τbc Q.T₀
      span_range_τ₁ := span_range_τbc Q.T₁
      τ₁_Pi₀ := fun t => by
        show (1 : C) ⊗ₜ[B] Q.Pi₀ t = (Q.Pi₀.baseChange C) ((1 : C) ⊗ₜ[B] t)
        rw [LinearMap.baseChange_tmul]
      τ₀_Pi₁ := fun t => by
        show (1 : C) ⊗ₜ[B] Q.Pi₁ t = (Q.Pi₁.baseChange C) ((1 : C) ⊗ₜ[B] t)
        rw [LinearMap.baseChange_tmul]
      u₀_eq := fun x' v hv hv' t s hs H => by
        have H' : Q.u₀ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x')))) =
            LocalizedModule.mk t ⟨s, hs⟩ := H
        show u₀Q S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q.N₀ (PrimeSpectrum.comap (algebraMap B C) x')))) = _
        rw [u₀Q_tmul, one_smul, H']
        exact β₀Q_mk S Q x' t s hs
      u₁_eq := fun x' v hv hv' t s hs H => by
        have H' : Q.u₁ (PrimeSpectrum.comap (algebraMap B C) x') ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) x')) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x')))) =
            LocalizedModule.mk t ⟨s, hs⟩ := H
        show u₁Q S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q.N₁ (PrimeSpectrum.comap (algebraMap B C) x')))) = _
        rw [u₁Q_tmul, one_smul, H']
        exact β₁Q_mk S Q x' t s hs }⟩⟩

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization (solution)
