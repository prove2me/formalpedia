-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3cddbd60-43bf-585d-964d-b44fbcbea8c4

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24D

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

end B24D

namespace B24D

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

end B24D

namespace B24D

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

end B24D

namespace B24D

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

end B24D

namespace B24D
section Chart

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (S : Submonoid B) [IsLocalization S A]
variable (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
variable (T' : Type) [AddCommGroup T'] [Module A T'] [Module.Invertible A T'] [Module B T'] [IsScalarTower B A T']
variable (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T') (hτ : Submodule.span A (Set.range τ) = ⊤)
variable (x : PrimeSpectrum B) (y : PrimeSpectrum A) (hy : PrimeSpectrum.comap (algebraMap B A) y = x)

include S hτ hy in
theorem isLocalizedModule_γ' : IsLocalizedModule x.asIdeal.primeCompl (γ T T' τ y) :=
  hy ▸ isLocalizedModule_γ S T T' τ hτ y

noncomputable def βx : stalk B x T ≃ₗ[B] stalk A y T' :=
  haveI := isLocalizedModule_γ' (𝒪 := 𝒪) S T T' τ hτ x y hy
  IsLocalizedModule.iso x.asIdeal.primeCompl (γ (𝒪 := 𝒪) T T' τ y)

include hy in
theorem mem_primeCompl_of {s : B} (hs : s ∈ x.asIdeal.primeCompl) : algebraMap B A s ∈ y.asIdeal.primeCompl := by
  subst hy; exact hs

theorem βx_mk (t : T) (s : B) (hs : s ∈ x.asIdeal.primeCompl) :
    βx (𝒪 := 𝒪) S T T' τ hτ x y hy (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk (τ t) (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl) := by
  haveI := isLocalizedModule_γ' (𝒪 := 𝒪) S T T' τ hτ x y hy
  show IsLocalizedModule.iso x.asIdeal.primeCompl (γ (𝒪 := 𝒪) T T' τ y) (LocalizedModule.mk t ⟨s, hs⟩) = _
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (γ (𝒪 := 𝒪) T T' τ y) ⟨s, hs⟩)).1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_smul, LocalizedModule.smul'_mk,
    ← algebraMap_smul A s (LocalizedModule.mk (τ t) (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl)),
    LocalizedModule.smul'_mk]
  have h1 : LocalizedModule.mk (s • t) (⟨s, hs⟩ : x.asIdeal.primeCompl) = LocalizedModule.mk t 1 :=
    LocalizedModule.mk_cancel ⟨s, hs⟩ t
  have h2 : LocalizedModule.mk (algebraMap B A s • τ t)
      (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl) = LocalizedModule.mk (τ t) 1 :=
    LocalizedModule.mk_cancel (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl) (τ t)
  rw [h1, h2, IsLocalizedModule.iso_mk_one, γ_apply]

end Chart

section ChartNat

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (S : Submonoid B) [IsLocalization S A]
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀]
variable (T₀' : Type) [AddCommGroup T₀'] [Module A T₀'] [Module.Invertible A T₀'] [Module B T₀'] [IsScalarTower B A T₀']
variable (τ₀ : T₀ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T₀') (hτ₀ : Submodule.span A (Set.range τ₀) = ⊤)
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁]
variable (T₁' : Type) [AddCommGroup T₁'] [Module A T₁'] [Module.Invertible A T₁'] [Module B T₁'] [IsScalarTower B A T₁']
variable (τ₁ : T₁ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T₁') (hτ₁ : Submodule.span A (Set.range τ₁) = ⊤)
variable (x : PrimeSpectrum B) (y : PrimeSpectrum A) (hy : PrimeSpectrum.comap (algebraMap B A) y = x)

theorem βx_natural (P : T₀ →ₗ[B] T₁) (P' : T₀' →ₗ[A] T₁') (hP : ∀ t, τ₁ (P t) = P' (τ₀ t)) (m : stalk B x T₀) :
    βx (𝒪 := 𝒪) S T₁ T₁' τ₁ hτ₁ x y hy (LocalizedModule.map x.asIdeal.primeCompl P m) =
      LocalizedModule.map y.asIdeal.primeCompl P' (βx (𝒪 := 𝒪) S T₀ T₀' τ₀ hτ₀ x y hy m) := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [map_mk, βx_mk S T₁ T₁' τ₁ hτ₁ x y hy (P t) s s.2, βx_mk S T₀ T₀' τ₀ hτ₀ x y hy t s s.2, map_mk, hP]

end ChartNat
end B24D

namespace B24D
section TauP
variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (g : B) [IsLocalization.Away g A]
variable (T : Type) [AddCommGroup T] [Module B T]
variable (T' : Type) [AddCommGroup T'] [Module A T'] [Module B T'] [IsScalarTower B A T']
variable (p : T →ₗ[B] T') [IsLocalizedModule (Submonoid.powers g) p]

def τp : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T' :=
  { toFun := p, map_add' := fun a b => map_add p a b, map_smul' := fun b t => by
      rw [map_smul]; show b • p t = algebraMap B A b • p t; exact (algebraMap_smul A b (p t)).symm }

theorem τp_apply (t : T) : τp (𝒪 := 𝒪) (A := A) T T' p t = p t := rfl

include g in
theorem span_range_τp : Submodule.span A (Set.range (τp (𝒪 := 𝒪) (A := A) T T' p)) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalizedModule.surj (Submonoid.powers g) p m
  have hunit : IsUnit (algebraMap B A s) := IsLocalization.map_units A s
  have : m = ((hunit.unit⁻¹ : Aˣ) : A) • p t := by
    rw [← hts, Submonoid.smul_def, ← algebraMap_smul A (s : B), smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec,
      one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
end TauP
end B24D

namespace B24D
section Transfer

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (SA : Submonoid B) [IsLocalization SA A]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (SC : Submonoid B) [IsLocalization SC C]
variable [Algebra A C] [IsScalarTower B A C] [IsScalarTower 𝒪 A C]
variable (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
variable (Q₁ : DrinfeldDatum (K := K) π A) (Q'' : DrinfeldDatum (K := K) π C)
variable [Module B Q₁.T₀] [IsScalarTower B A Q₁.T₀] [Module B Q₁.T₁] [IsScalarTower B A Q₁.T₁]
variable [Module B Q''.T₀] [IsScalarTower B C Q''.T₀] [Module B Q''.T₁] [IsScalarTower B C Q''.T₁]
variable (W : Q₁.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 A C) Q'')

theorem transfer₀
    (τA : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] Q₁.T₀) (hτA : Submodule.span A (Set.range τA) = ⊤)
    (q : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] Q''.T₀) (hq : Submodule.span C (Set.range q) = ⊤)
    (hqτ : ∀ t, q t = W.τ₀ (τA t))
    (x : PrimeSpectrum B) (w : PrimeSpectrum C) (hw : PrimeSpectrum.comap (algebraMap B C) w = x)
    (hy : PrimeSpectrum.comap (algebraMap B A) (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w) = x)
    (v : Fin 2 → K) (hv : v ∈ Q₁.N₀ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w)) (hv'' : v ∈ Q''.N₀ w)
    (m : stalk B x T)
    (H : Q₁.u₀ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w)
        ((1 : locRing A (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w)) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q₁.N₀ _))) =
      βx (𝒪 := 𝒪) SA T Q₁.T₀ τA hτA x _ hy m) :
    Q''.u₀ w ((1 : locRing C w) ⊗ₜ[𝒪] (⟨v, hv''⟩ : ↥(Q''.N₀ w))) = βx (𝒪 := 𝒪) SC T Q''.T₀ q hq x w hw m := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [βx_mk] at H
    rw [βx_mk, W.u₀_eq w v hv hv'' (τA t) (algebraMap B A s) (mem_primeCompl_of x _ hy s.2) H]
    congr 1
    · exact (hqτ t).symm
    · apply Subtype.ext
      show (IsScalarTower.toAlgHom 𝒪 A C) (algebraMap B A s) = algebraMap B C s
      rw [IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply]

theorem transfer₁
    (τA : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] Q₁.T₁) (hτA : Submodule.span A (Set.range τA) = ⊤)
    (q : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] Q''.T₁) (hq : Submodule.span C (Set.range q) = ⊤)
    (hqτ : ∀ t, q t = W.τ₁ (τA t))
    (x : PrimeSpectrum B) (w : PrimeSpectrum C) (hw : PrimeSpectrum.comap (algebraMap B C) w = x)
    (hy : PrimeSpectrum.comap (algebraMap B A) (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w) = x)
    (v : Fin 2 → K) (hv : v ∈ Q₁.N₁ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w)) (hv'' : v ∈ Q''.N₁ w)
    (m : stalk B x T)
    (H : Q₁.u₁ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w)
        ((1 : locRing A (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w)) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q₁.N₁ _))) =
      βx (𝒪 := 𝒪) SA T Q₁.T₁ τA hτA x _ hy m) :
    Q''.u₁ w ((1 : locRing C w) ⊗ₜ[𝒪] (⟨v, hv''⟩ : ↥(Q''.N₁ w))) = βx (𝒪 := 𝒪) SC T Q''.T₁ q hq x w hw m := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [βx_mk] at H
    rw [βx_mk, W.u₁_eq w v hv hv'' (τA t) (algebraMap B A s) (mem_primeCompl_of x _ hy s.2) H]
    congr 1
    · exact (hqτ t).symm
    · apply Subtype.ext
      show (IsScalarTower.toAlgHom 𝒪 A C) (algebraMap B A s) = algebraMap B C s
      rw [IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply]

end Transfer
end B24D

namespace B24D
section Geo

variable {B : Type} [CommRing B]

theorem exists_not_mem {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤) (x : PrimeSpectrum B) :
    ∃ i : Fin k, f i ∉ x.asIdeal := by
  by_contra h
  push_neg at h
  apply x.isPrime.ne_top
  rw [eq_top_iff, ← hf]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)

theorem exists_comap_eq {A : Type} [CommRing A] [Algebra B A] (g : B) [IsLocalization.Away g A]
    (x : PrimeSpectrum B) (hx : g ∉ x.asIdeal) : ∃ y : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap B A) y = x := by
  have : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]; exact hx
  exact this

theorem comap_injective {A : Type} [CommRing A] [Algebra B A] (g : B) [IsLocalization.Away g A]
    {y y' : PrimeSpectrum A} (h : PrimeSpectrum.comap (algebraMap B A) y = PrimeSpectrum.comap (algebraMap B A) y') :
    y = y' :=
  PrimeSpectrum.localization_comap_injective A (Submonoid.powers g) h

theorem comap_pointUnder {𝒪 : Type} [CommRing 𝒪] [Algebra 𝒪 B] {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [Algebra A C] [IsScalarTower B A C] [IsScalarTower 𝒪 A C]
    (w : PrimeSpectrum C) :
    PrimeSpectrum.comap (algebraMap B A) (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w) =
      PrimeSpectrum.comap (algebraMap B C) w := by
  apply PrimeSpectrum.ext
  ext b
  show algebraMap A C (algebraMap B A b) ∈ w.asIdeal ↔ algebraMap B C b ∈ w.asIdeal
  rw [← IsScalarTower.algebraMap_apply]

end Geo

section Span

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable [Algebra A C] [IsScalarTower B A C] [IsScalarTower 𝒪 A C]
variable {T : Type} [AddCommGroup T] [Module B T]
variable {T' : Type} [AddCommGroup T'] [Module A T']
variable {T'' : Type} [AddCommGroup T''] [Module C T'']

def compσ (σ : T' →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] T'')
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T') :
    T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T'' :=
  { toFun := fun t => σ (τ t)
    map_add' := fun a b => by rw [map_add, map_add]
    map_smul' := fun b t => by
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
      show (IsScalarTower.toAlgHom 𝒪 A C) ((IsScalarTower.toAlgHom 𝒪 B A) b) • σ (τ t) = algebraMap B C b • σ (τ t)
      rw [IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply] }

theorem compσ_apply (σ : T' →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] T'')
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T') (t : T) : compσ σ τ t = σ (τ t) := rfl

theorem span_range_compσ (σ : T' →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] T'')
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T')
    (hσ : Submodule.span C (Set.range σ) = ⊤) (hτ : Submodule.span A (Set.range τ) = ⊤) :
    Submodule.span C (Set.range (compσ σ τ)) = ⊤ := by

  have key : ∀ t' : T', σ t' ∈ Submodule.span C (Set.range (compσ σ τ)) := by
    intro t'
    have ht' : t' ∈ Submodule.span A (Set.range τ) := by rw [hτ]; exact Submodule.mem_top
    induction ht' using Submodule.span_induction with
    | mem u hu => obtain ⟨t, rfl⟩ := hu; exact Submodule.subset_span ⟨t, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul a u _ hu => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hu
  rw [eq_top_iff, ← hσ]
  apply Submodule.span_le.mpr
  rintro _ ⟨t', rfl⟩
  exact key t'

end Span
end B24D

theorem B24D.range_le_smul_top_of_isLocalizedModule
    {B : Type} [CommRing B] {A : Type} [CommRing A] [Algebra B A] (g : B) [IsLocalization.Away g A]
    {T₀ T₁ : Type} [AddCommGroup T₀] [Module B T₀] [AddCommGroup T₁] [Module B T₁]
    {T₀' T₁' : Type} [AddCommGroup T₀'] [Module A T₀'] [Module B T₀'] [IsScalarTower B A T₀']
    [AddCommGroup T₁'] [Module A T₁'] [Module B T₁'] [IsScalarTower B A T₁']
    (p₀ : T₀ →ₗ[B] T₀') [IsLocalizedModule (Submonoid.powers g) p₀] (p₁ : T₁ →ₗ[B] T₁')
    (P : T₀ →ₗ[B] T₁) (P' : T₀' →ₗ[A] T₁') (hP : ∀ t, p₁ (P t) = P' (p₀ t))
    (y : PrimeSpectrum A)
    (h : LinearMap.range P ≤ (PrimeSpectrum.comap (algebraMap B A) y).asIdeal • (⊤ : Submodule B T₁)) :
    LinearMap.range P' ≤ y.asIdeal • (⊤ : Submodule A T₁') := by

  have key : ∀ m : T₁, m ∈ (PrimeSpectrum.comap (algebraMap B A) y).asIdeal • (⊤ : Submodule B T₁) →
      p₁ m ∈ y.asIdeal • (⊤ : Submodule A T₁') := by
    intro m hm
    refine Submodule.smul_induction_on hm (fun b hb n _ => ?_) (fun m₁ m₂ h₁ h₂ => ?_)
    · have hb' : algebraMap B A b ∈ y.asIdeal := by
        rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hb
        exact hb
      rw [LinearMap.map_smul, ← algebraMap_smul A b (p₁ n)]
      exact Submodule.smul_mem_smul hb' Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ h₁ h₂
  rintro _ ⟨t', rfl⟩
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalizedModule.surj (Submonoid.powers g) p₀ t'
  obtain ⟨u, hu⟩ := IsLocalization.map_units A s
  have e1 : P' (p₀ t) = (algebraMap B A (s : B)) • P' t' := by
    rw [← hts, Submonoid.smul_def, ← algebraMap_smul A (s : B) t', LinearMap.map_smul]
  have e2 : P' t' = ((u⁻¹ : Aˣ) : A) • P' (p₀ t) := by
    rw [e1, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [e2, ← hP]
  exact Submodule.smul_mem _ _ (key _ (h ⟨t, rfl⟩))

theorem B24D.map_smul_top_le
    {B : Type} [CommRing B] {A : Type} [CommRing A] [Algebra B A] (y : PrimeSpectrum A)
    {M : Type} [AddCommGroup M] [Module B M]
    {M' : Type} [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower B A M']
    (e : M →ₗ[B] M') :
    ((PrimeSpectrum.comap (algebraMap B A) y).asIdeal • (⊤ : Submodule B M)).map e ≤
      (y.asIdeal • (⊤ : Submodule A M')).restrictScalars B := by
  rintro _ ⟨m, hm, rfl⟩
  rw [Submodule.restrictScalars_mem]
  refine Submodule.smul_induction_on hm (fun b hb n _ => ?_) (fun m₁ m₂ h₁ h₂ => ?_)
  · have hb' : algebraMap B A b ∈ y.asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hb
      exact hb
    rw [LinearMap.map_smul, ← algebraMap_smul A b (e n)]
    exact Submodule.smul_mem_smul hb' Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

namespace B24D
theorem inclBaseChange_inclBaseChange {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    (B : Type) [CommRing B] [Algebra 𝒪 B] (M M' : FullLattice 𝒪 K) (h : M'.1 = M.1) (p : latticeBaseChange 𝒪 K B M) :
    inclBaseChange B (M' := M') (M := M) (le_of_eq h) (inclBaseChange B (M' := M) (M := M') (le_of_eq h.symm) p) = p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul b w =>
    rw [show inclBaseChange B (M' := M) (M := M') (le_of_eq h.symm) (b ⊗ₜ[𝒪] w) = b ⊗ₜ[𝒪] Submodule.inclusion (le_of_eq h.symm) w
        from LinearMap.baseChange_tmul _ _ _,
      show inclBaseChange B (M' := M') (M := M) (le_of_eq h) (b ⊗ₜ[𝒪] Submodule.inclusion (le_of_eq h.symm) w) =
        b ⊗ₜ[𝒪] Submodule.inclusion (le_of_eq h) (Submodule.inclusion (le_of_eq h.symm) w) from LinearMap.baseChange_tmul _ _ _]
    rfl
end B24D

namespace B24D
section Assembly

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

include hιυ in
theorem not_mem_ι (x : PrimeSpectrum B) : f (ι x) ∉ x.asIdeal := by
  have : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x))))) := ⟨υ x, hιυ x⟩
  rwa [PrimeSpectrum.localization_away_comap_range _ (f (ι x))] at this

include hN₀ hιυ in
theorem mem_chart₀ (x : PrimeSpectrum B) {v : Fin 2 → K} (hv : v ∈ N₀g x) : v ∈ (Q (ι x)).N₀ (υ x) := by
  rw [← hN₀ (ι x) (υ x), hιυ x]; exact hv

include hN₀ hιυ in
theorem eq_chart₀ (x : PrimeSpectrum B) : N₀g x = (Q (ι x)).N₀ (υ x) := by
  rw [← hN₀ (ι x) (υ x), hιυ x]

include hN₀ hιυ in
theorem full₀g (x : PrimeSpectrum B) : LT.LatticeTree.IsFullLattice (N₀g x) := by
  rw [eq_chart₀ f Q N₀g hN₀ ι υ hιυ x]; exact (Q (ι x)).full₀ (υ x)

noncomputable abbrev βι₀ (x : PrimeSpectrum B) : stalk B x T₀ ≃ₗ[B] stalk (Localization.Away (f (ι x))) (υ x) (Q (ι x)).T₀ :=
  βx (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) T₀ (Q (ι x)).T₀
    (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
    (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))) x (υ x) (hιυ x)

noncomputable def gg₀ (x : PrimeSpectrum B) : ↥(N₀g x) →ₗ[𝒪] stalk B x T₀ :=
  { toFun := fun v => (βι₀ f Q T₀ p₀ ι υ hιυ x).symm
      ((Q (ι x)).u₀ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩))
    map_add' := fun a b => by
      show (βι₀ f Q T₀ p₀ ι υ hιυ x).symm _ = (βι₀ f Q T₀ p₀ ι υ hιυ x).symm _ + (βι₀ f Q T₀ p₀ ι υ hιυ x).symm _
      rw [← map_add, ← map_add, ← TensorProduct.tmul_add]; rfl
    map_smul' := fun r v => by
      show (βι₀ f Q T₀ p₀ ι υ hιυ x).symm _ = r • (βι₀ f Q T₀ p₀ ι υ hιυ x).symm _
      rw [← algebraMap_smul B r ((βι₀ f Q T₀ p₀ ι υ hιυ x).symm _), ← map_smul,
        ← algebraMap_smul (locRing (Localization.Away (f (ι x))) (υ x)) (algebraMap 𝒪 B r),
        ← IsScalarTower.algebraMap_apply, ← map_smul, algebraMap_smul, ← TensorProduct.tmul_smul]
      rfl }

noncomputable def ug₀ (x : PrimeSpectrum B) :
    latticeBaseChange 𝒪 K (locRing B x) (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K) →ₗ[locRing B x]
      stalk B x T₀ :=
  (gg₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x).liftBaseChange (locRing B x)

theorem ug₀_tmul (x : PrimeSpectrum B) (a : locRing B x) (v : ↥(N₀g x)) :
    ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x (a ⊗ₜ[𝒪] v) = a • (βι₀ f Q T₀ p₀ ι υ hιυ x).symm
      ((Q (ι x)).u₀ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

include hN₁ hιυ in
theorem mem_chart₁ (x : PrimeSpectrum B) {v : Fin 2 → K} (hv : v ∈ N₁g x) : v ∈ (Q (ι x)).N₁ (υ x) := by
  rw [← hN₁ (ι x) (υ x), hιυ x]; exact hv

include hN₁ hιυ in
theorem eq_chart₁ (x : PrimeSpectrum B) : N₁g x = (Q (ι x)).N₁ (υ x) := by
  rw [← hN₁ (ι x) (υ x), hιυ x]

include hN₁ hιυ in
theorem full₁g (x : PrimeSpectrum B) : LT.LatticeTree.IsFullLattice (N₁g x) := by
  rw [eq_chart₁ f Q N₁g hN₁ ι υ hιυ x]; exact (Q (ι x)).full₁ (υ x)

noncomputable abbrev βι₁ (x : PrimeSpectrum B) : stalk B x T₁ ≃ₗ[B] stalk (Localization.Away (f (ι x))) (υ x) (Q (ι x)).T₁ :=
  βx (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) T₁ (Q (ι x)).T₁
    (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
    (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))) x (υ x) (hιυ x)

noncomputable def gg₁ (x : PrimeSpectrum B) : ↥(N₁g x) →ₗ[𝒪] stalk B x T₁ :=
  { toFun := fun v => (βι₁ f Q T₁ p₁ ι υ hιυ x).symm
      ((Q (ι x)).u₁ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, mem_chart₁ f Q N₁g hN₁ ι υ hιυ x v.2⟩))
    map_add' := fun a b => by
      show (βι₁ f Q T₁ p₁ ι υ hιυ x).symm _ = (βι₁ f Q T₁ p₁ ι υ hιυ x).symm _ + (βι₁ f Q T₁ p₁ ι υ hιυ x).symm _
      rw [← map_add, ← map_add, ← TensorProduct.tmul_add]; rfl
    map_smul' := fun r v => by
      show (βι₁ f Q T₁ p₁ ι υ hιυ x).symm _ = r • (βι₁ f Q T₁ p₁ ι υ hιυ x).symm _
      rw [← algebraMap_smul B r ((βι₁ f Q T₁ p₁ ι υ hιυ x).symm _), ← map_smul,
        ← algebraMap_smul (locRing (Localization.Away (f (ι x))) (υ x)) (algebraMap 𝒪 B r),
        ← IsScalarTower.algebraMap_apply, ← map_smul, algebraMap_smul, ← TensorProduct.tmul_smul]
      rfl }

noncomputable def ug₁ (x : PrimeSpectrum B) :
    latticeBaseChange 𝒪 K (locRing B x) (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K) →ₗ[locRing B x]
      stalk B x T₁ :=
  (gg₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x).liftBaseChange (locRing B x)

theorem ug₁_tmul (x : PrimeSpectrum B) (a : locRing B x) (v : ↥(N₁g x)) :
    ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x (a ⊗ₜ[𝒪] v) = a • (βι₁ f Q T₁ p₁ ι υ hιυ x).symm
      ((Q (ι x)).u₁ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, mem_chart₁ f Q N₁g hN₁ ι υ hιυ x v.2⟩)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

end Assembly
end B24D

namespace B24D
section Overlap

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

variable (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
variable [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
variable [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
variable [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
variable [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
variable (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
variable [∀ i j, Module B (Q₂ i j).T₀] [∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₀]
variable [∀ i j, Module B (Q₂ i j).T₁] [∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₁]
variable (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
variable (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
variable (hc₀ : ∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t))
variable (hc₁ : ∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t))

include hN₀ hc₀ in

theorem chart₀ (x : PrimeSpectrum B) (j : Fin k) (z : PrimeSpectrum (Localization.Away (f j)))
    (hz : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z = x)
    (v : Fin 2 → K) (hv : v ∈ N₀g x) (hv' : v ∈ (Q j).N₀ z) :
    (Q j).u₀ z ((1 : locRing (Localization.Away (f j)) z) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥((Q j).N₀ z))) =
      βx (𝒪 := 𝒪) (Submonoid.powers (f j)) T₀ (Q j).T₀
        (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₀ (Q j).T₀ (p₀ j)) (span_range_τp (f j) T₀ (Q j).T₀ (p₀ j)) x z hz
        (ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₀g x)))) := by

  have hfj : f j ∉ x.asIdeal := by
    have : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f j)))) := ⟨z, hz⟩
    rwa [PrimeSpectrum.localization_away_comap_range _ (f j)] at this
  have hfij : f (ι x) * f j ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim (not_mem_ι f ι υ hιυ x) hfj
  obtain ⟨w, hw⟩ := exists_comap_eq (A := C (ι x) j) (f (ι x) * f j) x hfij
  have hwl : PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x))))
      (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w) = x := by
    rw [comap_pointUnder]; exact hw
  have hwr : PrimeSpectrum.comap (algebraMap B (Localization.Away (f j)))
      (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w) = x := by
    rw [comap_pointUnder]; exact hw
  have hwy : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w = υ x :=
    comap_injective (f (ι x)) (hwl.trans (hιυ x).symm)
  have hwz : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w = z :=
    comap_injective (f j) (hwr.trans hz.symm)

  set m := ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₀g x))) with hm
  have Hi : ∀ (y' : PrimeSpectrum (Localization.Away (f (ι x))))
      (hy' : PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y' = x) (hvy' : v ∈ (Q (ι x)).N₀ y'),
      y' = υ x → (Q (ι x)).u₀ y' ((1 : locRing (Localization.Away (f (ι x))) y') ⊗ₜ[𝒪] (⟨v, hvy'⟩ : ↥((Q (ι x)).N₀ y'))) =
        βx (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) T₀ (Q (ι x)).T₀
          (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
          (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))) x y' hy' m := by
    rintro y' hy' hvy' rfl
    rw [hm, ug₀_tmul, one_smul, LinearEquiv.apply_symm_apply]
  set m' := (βx (𝒪 := 𝒪) (Submonoid.powers (f j)) T₀ (Q j).T₀
        (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₀ (Q j).T₀ (p₀ j)) (span_range_τp (f j) T₀ (Q j).T₀ (p₀ j)) x z hz).symm
      ((Q j).u₀ z ((1 : locRing (Localization.Away (f j)) z) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥((Q j).N₀ z)))) with hm'
  have Hj : ∀ (z' : PrimeSpectrum (Localization.Away (f j)))
      (hz' : PrimeSpectrum.comap (algebraMap B (Localization.Away (f j))) z' = x) (hvz' : v ∈ (Q j).N₀ z'),
      z' = z → (Q j).u₀ z' ((1 : locRing (Localization.Away (f j)) z') ⊗ₜ[𝒪] (⟨v, hvz'⟩ : ↥((Q j).N₀ z'))) =
        βx (𝒪 := 𝒪) (Submonoid.powers (f j)) T₀ (Q j).T₀
          (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₀ (Q j).T₀ (p₀ j))
          (span_range_τp (f j) T₀ (Q j).T₀ (p₀ j)) x z' hz' m' := by
    rintro z' hz' hvz' rfl
    rw [hm', LinearEquiv.apply_symm_apply]
  have hv'' : v ∈ (Q₂ (ι x) j).N₀ w := by
    rw [(Wl (ι x) j).N₀_eq w, hwy]; exact mem_chart₀ f Q N₀g hN₀ ι υ hιυ x hv
  have hvl : v ∈ (Q (ι x)).N₀ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w) := by
    rw [hwy]; exact mem_chart₀ f Q N₀g hN₀ ι υ hιυ x hv
  have hvr : v ∈ (Q j).N₀ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w) := by
    rw [hwz]; exact hv'
  have H1 := transfer₀ (Submonoid.powers (f (ι x))) (Submonoid.powers (f (ι x) * f j)) T₀ (Q (ι x)) (Q₂ (ι x) j) (Wl (ι x) j)
    (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
    (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
    (compσ (Wl (ι x) j).τ₀ (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x))))
    (span_range_compσ _ _ (Wl (ι x) j).span_range_τ₀ (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))))
    (fun t => rfl) x w hw hwl v hvl hv'' m (Hi _ hwl hvl hwy)
  have H2 := transfer₀ (Submonoid.powers (f j)) (Submonoid.powers (f (ι x) * f j)) T₀ (Q j) (Q₂ (ι x) j) (Wr (ι x) j)
    (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₀ (Q j).T₀ (p₀ j))
    (span_range_τp (f j) T₀ (Q j).T₀ (p₀ j))
    (compσ (Wl (ι x) j).τ₀ (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x))))
    (span_range_compσ _ _ (Wl (ι x) j).span_range_τ₀ (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))))
    (fun t => hc₀ (ι x) j t) x w hw hwr v hvr hv'' m' (Hj _ hwr hvr hwz)
  have hmm' : m = m' := (βx _ _ _ _ _ _ _ _).injective (H1.symm.trans H2)
  rw [Hj z hz hv' rfl, ← hmm']

include hN₁ hc₁ in

theorem chart₁ (x : PrimeSpectrum B) (j : Fin k) (z : PrimeSpectrum (Localization.Away (f j)))
    (hz : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z = x)
    (v : Fin 2 → K) (hv : v ∈ N₁g x) (hv' : v ∈ (Q j).N₁ z) :
    (Q j).u₁ z ((1 : locRing (Localization.Away (f j)) z) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥((Q j).N₁ z))) =
      βx (𝒪 := 𝒪) (Submonoid.powers (f j)) T₁ (Q j).T₁
        (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₁ (Q j).T₁ (p₁ j)) (span_range_τp (f j) T₁ (Q j).T₁ (p₁ j)) x z hz
        (ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₁g x)))) := by

  have hfj : f j ∉ x.asIdeal := by
    have : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f j)))) := ⟨z, hz⟩
    rwa [PrimeSpectrum.localization_away_comap_range _ (f j)] at this
  have hfij : f (ι x) * f j ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim (not_mem_ι f ι υ hιυ x) hfj
  obtain ⟨w, hw⟩ := exists_comap_eq (A := C (ι x) j) (f (ι x) * f j) x hfij
  have hwl : PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x))))
      (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w) = x := by
    rw [comap_pointUnder]; exact hw
  have hwr : PrimeSpectrum.comap (algebraMap B (Localization.Away (f j)))
      (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w) = x := by
    rw [comap_pointUnder]; exact hw
  have hwy : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w = υ x :=
    comap_injective (f (ι x)) (hwl.trans (hιυ x).symm)
  have hwz : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w = z :=
    comap_injective (f j) (hwr.trans hz.symm)

  set m := ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₁g x))) with hm
  have Hi : ∀ (y' : PrimeSpectrum (Localization.Away (f (ι x))))
      (hy' : PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y' = x) (hvy' : v ∈ (Q (ι x)).N₁ y'),
      y' = υ x → (Q (ι x)).u₁ y' ((1 : locRing (Localization.Away (f (ι x))) y') ⊗ₜ[𝒪] (⟨v, hvy'⟩ : ↥((Q (ι x)).N₁ y'))) =
        βx (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) T₁ (Q (ι x)).T₁
          (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
          (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))) x y' hy' m := by
    rintro y' hy' hvy' rfl
    rw [hm, ug₁_tmul, one_smul, LinearEquiv.apply_symm_apply]
  set m' := (βx (𝒪 := 𝒪) (Submonoid.powers (f j)) T₁ (Q j).T₁
        (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₁ (Q j).T₁ (p₁ j)) (span_range_τp (f j) T₁ (Q j).T₁ (p₁ j)) x z hz).symm
      ((Q j).u₁ z ((1 : locRing (Localization.Away (f j)) z) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥((Q j).N₁ z)))) with hm'
  have Hj : ∀ (z' : PrimeSpectrum (Localization.Away (f j)))
      (hz' : PrimeSpectrum.comap (algebraMap B (Localization.Away (f j))) z' = x) (hvz' : v ∈ (Q j).N₁ z'),
      z' = z → (Q j).u₁ z' ((1 : locRing (Localization.Away (f j)) z') ⊗ₜ[𝒪] (⟨v, hvz'⟩ : ↥((Q j).N₁ z'))) =
        βx (𝒪 := 𝒪) (Submonoid.powers (f j)) T₁ (Q j).T₁
          (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₁ (Q j).T₁ (p₁ j))
          (span_range_τp (f j) T₁ (Q j).T₁ (p₁ j)) x z' hz' m' := by
    rintro z' hz' hvz' rfl
    rw [hm', LinearEquiv.apply_symm_apply]
  have hv'' : v ∈ (Q₂ (ι x) j).N₁ w := by
    rw [(Wl (ι x) j).N₁_eq w, hwy]; exact mem_chart₁ f Q N₁g hN₁ ι υ hιυ x hv
  have hvl : v ∈ (Q (ι x)).N₁ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w) := by
    rw [hwy]; exact mem_chart₁ f Q N₁g hN₁ ι υ hιυ x hv
  have hvr : v ∈ (Q j).N₁ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w) := by
    rw [hwz]; exact hv'
  have H1 := transfer₁ (Submonoid.powers (f (ι x))) (Submonoid.powers (f (ι x) * f j)) T₁ (Q (ι x)) (Q₂ (ι x) j) (Wl (ι x) j)
    (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
    (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
    (compσ (Wl (ι x) j).τ₁ (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x))))
    (span_range_compσ _ _ (Wl (ι x) j).span_range_τ₁ (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))))
    (fun t => rfl) x w hw hwl v hvl hv'' m (Hi _ hwl hvl hwy)
  have H2 := transfer₁ (Submonoid.powers (f j)) (Submonoid.powers (f (ι x) * f j)) T₁ (Q j) (Q₂ (ι x) j) (Wr (ι x) j)
    (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) T₁ (Q j).T₁ (p₁ j))
    (span_range_τp (f j) T₁ (Q j).T₁ (p₁ j))
    (compσ (Wl (ι x) j).τ₁ (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x))))
    (span_range_compσ _ _ (Wl (ι x) j).span_range_τ₁ (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))))
    (fun t => hc₁ (ι x) j t) x w hw hwr v hvr hv'' m' (Hj _ hwr hvr hwz)
  have hmm' : m = m' := (βx _ _ _ _ _ _ _ _).injective (H1.symm.trans H2)
  rw [Hj z hz hv' rfl, ← hmm']

end Overlap
end B24D

namespace B24D
section Fields

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

variable (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀)
variable (hPi₀ : ∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) (hPi₁ : ∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t))

theorem βι_ug₀ (x : PrimeSpectrum B) (v : ↥(N₀g x)) :
    βι₀ f Q T₀ p₀ ι υ hιυ x (ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] v)) =
      (Q (ι x)).u₀ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩) := by
  rw [ug₀_tmul, one_smul, LinearEquiv.apply_symm_apply]

theorem ug₀_ιB (x : PrimeSpectrum B) (p' : latticeBaseChange 𝒪 K B (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) :
    βι₀ f Q T₀ p₀ ι υ hιυ x (ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x (ιB (locRing B x) _ p')) =
      (Q (ι x)).u₀ (υ x) (ιB (locRing (Localization.Away (f (ι x))) (υ x)) ((Q (ι x)).L₀ (υ x))
        (inclBaseChange B (M' := (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (M := (Q (ι x)).L₀ (υ x))
          (le_of_eq (eq_chart₀ f Q N₀g hN₀ ι υ hιυ x)) p')) := by
  induction p' using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) =
        b • ((1 : B) ⊗ₜ[𝒪] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e2 : inclBaseChange B (M' := (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (M := (Q (ι x)).L₀ (υ x))
          (le_of_eq (eq_chart₀ f Q N₀g hN₀ ι υ hιυ x)) (b ⊗ₜ[𝒪] v) =
        b • ((1 : B) ⊗ₜ[𝒪] (⟨v, mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩ : ↥((Q (ι x)).N₀ (υ x)))) := by
      rw [e1, map_smul]; try rfl
    rw [e2, e1, map_smul, ιB_one_tmul, LinearMap.map_smul_of_tower, map_smul, βι_ug₀,
      map_smul, ιB_one_tmul, LinearMap.map_smul_of_tower]

theorem ug₀_surjective (x : PrimeSpectrum B) : Function.Surjective (ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x) := by
  intro m
  obtain ⟨p', hp'⟩ := (Q (ι x)).u₀_surjective (υ x) (βι₀ f Q T₀ p₀ ι υ hιυ x m)
  haveI : IsScalarTower B (Localization.Away (f (ι x))) (locRing (Localization.Away (f (ι x))) (υ x)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower 𝒪 B (locRing (Localization.Away (f (ι x))) (υ x)) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply 𝒪 (Localization.Away (f (ι x))) (locRing _ (υ x)),
      IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f (ι x)))]; rfl)
  haveI : IsLocalization x.asIdeal.primeCompl (locRing (Localization.Away (f (ι x))) (υ x)) := by
    have h := isLocalization_atPrime_locRing (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) (υ x)
    rwa [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x] at h
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing (Localization.Away (f (ι x))) (υ x)) x.asIdeal.primeCompl ((Q (ι x)).L₀ (υ x))
  obtain ⟨⟨p₀', s⟩, hsp⟩ := IsLocalizedModule.surj x.asIdeal.primeCompl (ιB (locRing (Localization.Away (f (ι x))) (υ x)) ((Q (ι x)).L₀ (υ x))) p'
  have hunit : IsUnit (algebraMap B (locRing B x) s) := IsLocalization.map_units (locRing B x) s
  have key : ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x (ιB (locRing B x) _
      (inclBaseChange B (M' := (Q (ι x)).L₀ (υ x)) (M := (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (le_of_eq (eq_chart₀ f Q N₀g hN₀ ι υ hιυ x).symm) p₀')) =
      (s : B) • m := by
    apply (βι₀ f Q T₀ p₀ ι υ hιυ x).injective
    rw [ug₀_ιB, inclBaseChange_inclBaseChange B ((Q (ι x)).L₀ (υ x)) (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K) (eq_chart₀ f Q N₀g hN₀ ι υ hιυ x) p₀', ← hsp, Submonoid.smul_def, LinearMap.map_smul_of_tower, hp', map_smul]
  refine ⟨((hunit.unit⁻¹ : (locRing B x)ˣ) : locRing B x) • ιB (locRing B x) _
      (inclBaseChange B (M' := (Q (ι x)).L₀ (υ x)) (M := (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (le_of_eq (eq_chart₀ f Q N₀g hN₀ ι υ hιυ x).symm) p₀'), ?_⟩
  rw [map_smul, key, ← algebraMap_smul (locRing B x) (s : B) m, smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]

include hN₀ ι υ hιυ hPi₀ in
theorem ug₀_hasDetIndex (x : PrimeSpectrum B)
    (h : LinearMap.range Pi₀ ≤ x.asIdeal • (⊤ : Submodule B T₁)) :
    HasDetIndex π (N₀g x) 0 := by
  rw [eq_chart₀ f Q N₀g hN₀ ι υ hιυ x]
  apply (Q (ι x)).hasDetIndex₀ (υ x)
  apply range_le_smul_top_of_isLocalizedModule (f (ι x)) (p₀ (ι x)) (p₁ (ι x)) Pi₀ ((Q (ι x)).Pi₀) (hPi₀ (ι x)) (υ x)
  rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]
  exact h

theorem βι_ug₁ (x : PrimeSpectrum B) (v : ↥(N₁g x)) :
    βι₁ f Q T₁ p₁ ι υ hιυ x (ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] v)) =
      (Q (ι x)).u₁ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, mem_chart₁ f Q N₁g hN₁ ι υ hιυ x v.2⟩) := by
  rw [ug₁_tmul, one_smul, LinearEquiv.apply_symm_apply]

theorem ug₁_ιB (x : PrimeSpectrum B) (p' : latticeBaseChange 𝒪 K B (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) :
    βι₁ f Q T₁ p₁ ι υ hιυ x (ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x (ιB (locRing B x) _ p')) =
      (Q (ι x)).u₁ (υ x) (ιB (locRing (Localization.Away (f (ι x))) (υ x)) ((Q (ι x)).L₁ (υ x))
        (inclBaseChange B (M' := (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (M := (Q (ι x)).L₁ (υ x))
          (le_of_eq (eq_chart₁ f Q N₁g hN₁ ι υ hιυ x)) p')) := by
  induction p' using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) =
        b • ((1 : B) ⊗ₜ[𝒪] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e2 : inclBaseChange B (M' := (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (M := (Q (ι x)).L₁ (υ x))
          (le_of_eq (eq_chart₁ f Q N₁g hN₁ ι υ hιυ x)) (b ⊗ₜ[𝒪] v) =
        b • ((1 : B) ⊗ₜ[𝒪] (⟨v, mem_chart₁ f Q N₁g hN₁ ι υ hιυ x v.2⟩ : ↥((Q (ι x)).N₁ (υ x)))) := by
      rw [e1, map_smul]; try rfl
    rw [e2, e1, map_smul, ιB_one_tmul, LinearMap.map_smul_of_tower, map_smul, βι_ug₁,
      map_smul, ιB_one_tmul, LinearMap.map_smul_of_tower]

theorem ug₁_surjective (x : PrimeSpectrum B) : Function.Surjective (ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x) := by
  intro m
  obtain ⟨p', hp'⟩ := (Q (ι x)).u₁_surjective (υ x) (βι₁ f Q T₁ p₁ ι υ hιυ x m)
  haveI : IsScalarTower B (Localization.Away (f (ι x))) (locRing (Localization.Away (f (ι x))) (υ x)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower 𝒪 B (locRing (Localization.Away (f (ι x))) (υ x)) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply 𝒪 (Localization.Away (f (ι x))) (locRing _ (υ x)),
      IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f (ι x)))]; rfl)
  haveI : IsLocalization x.asIdeal.primeCompl (locRing (Localization.Away (f (ι x))) (υ x)) := by
    have h := isLocalization_atPrime_locRing (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) (υ x)
    rwa [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x] at h
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing (Localization.Away (f (ι x))) (υ x)) x.asIdeal.primeCompl ((Q (ι x)).L₁ (υ x))
  obtain ⟨⟨p₀', s⟩, hsp⟩ := IsLocalizedModule.surj x.asIdeal.primeCompl (ιB (locRing (Localization.Away (f (ι x))) (υ x)) ((Q (ι x)).L₁ (υ x))) p'
  have hunit : IsUnit (algebraMap B (locRing B x) s) := IsLocalization.map_units (locRing B x) s
  have key : ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x (ιB (locRing B x) _
      (inclBaseChange B (M' := (Q (ι x)).L₁ (υ x)) (M := (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (le_of_eq (eq_chart₁ f Q N₁g hN₁ ι υ hιυ x).symm) p₀')) =
      (s : B) • m := by
    apply (βι₁ f Q T₁ p₁ ι υ hιυ x).injective
    rw [ug₁_ιB, inclBaseChange_inclBaseChange B ((Q (ι x)).L₁ (υ x)) (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K) (eq_chart₁ f Q N₁g hN₁ ι υ hιυ x) p₀', ← hsp, Submonoid.smul_def, LinearMap.map_smul_of_tower, hp', map_smul]
  refine ⟨((hunit.unit⁻¹ : (locRing B x)ˣ) : locRing B x) • ιB (locRing B x) _
      (inclBaseChange B (M' := (Q (ι x)).L₁ (υ x)) (M := (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (le_of_eq (eq_chart₁ f Q N₁g hN₁ ι υ hιυ x).symm) p₀'), ?_⟩
  rw [map_smul, key, ← algebraMap_smul (locRing B x) (s : B) m, smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]

include hN₁ ι υ hιυ hPi₁ in
theorem ug₁_hasDetIndex (x : PrimeSpectrum B)
    (h : LinearMap.range Pi₁ ≤ x.asIdeal • (⊤ : Submodule B T₀)) :
    HasDetIndex π (N₁g x) (-1) := by
  rw [eq_chart₁ f Q N₁g hN₁ ι υ hιυ x]
  apply (Q (ι x)).hasDetIndex₁ (υ x)
  apply range_le_smul_top_of_isLocalizedModule (f (ι x)) (p₁ (ι x)) (p₀ (ι x)) Pi₁ ((Q (ι x)).Pi₁) (hPi₁ (ι x)) (υ x)
  rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]
  exact h

end Fields
end B24D

namespace B24D
section Fields2

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

variable (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀)
variable (hPi₀ : ∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) (hPi₁ : ∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t))

include hN₀ hN₁ hPi₁ in
theorem ug₀_injective (x : PrimeSpectrum B) (v : ↥(N₀g x))
    (h : ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₁)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x T₀))) :
    ∃ w ∈ N₁g x, (v : Fin 2 → K) = algebraMap 𝒪 K π • w := by
  have h' : (Q (ι x)).u₀ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪]
        (⟨v, mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩ : ↥((Q (ι x)).N₀ (υ x)))) ∈
      (LinearMap.range (LocalizedModule.map (υ x).asIdeal.primeCompl (Q (ι x)).Pi₁)).restrictScalars (Localization.Away (f (ι x))) ⊔
        (υ x).asIdeal • (⊤ : Submodule (Localization.Away (f (ι x))) (stalk (Localization.Away (f (ι x))) (υ x) (Q (ι x)).T₀)) := by
    rw [← βι_ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x v]
    obtain ⟨r, hr, z, hz, hrz⟩ := Submodule.mem_sup.mp h
    rw [← hrz, map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr ⊢
      obtain ⟨a, rfl⟩ := hr
      exact ⟨βι₁ f Q T₁ p₁ ι υ hιυ x a,
        (βx_natural (Submonoid.powers (f (ι x))) T₁ (Q (ι x)).T₁
          (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
          (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
          T₀ (Q (ι x)).T₀ (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
          (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))) x (υ x) (hιυ x) Pi₁ (Q (ι x)).Pi₁
          (fun t => hPi₁ (ι x) t) a).symm⟩
    · have hz' : z ∈ ((PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x)).asIdeal • ⊤ :
          Submodule B (stalk B x T₀)) := by
        rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]; exact hz
      exact map_smul_top_le (υ x) (βι₀ f Q T₀ p₀ ι υ hιυ x).toLinearMap (Submodule.mem_map_of_mem hz')
  obtain ⟨w, hw, hvw⟩ := (Q (ι x)).injective₀ (υ x) _ h'
  exact ⟨w, by rw [eq_chart₁ f Q N₁g hN₁ ι υ hιυ x]; exact hw, hvw⟩

include hN₁ hN₀ hPi₀ in
theorem ug₁_injective (x : PrimeSpectrum B) (v : ↥(N₁g x))
    (h : ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₀)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x T₁))) :
    (v : Fin 2 → K) ∈ N₀g x := by
  have h' : (Q (ι x)).u₁ (υ x) ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪]
        (⟨v, mem_chart₁ f Q N₁g hN₁ ι υ hιυ x v.2⟩ : ↥((Q (ι x)).N₁ (υ x)))) ∈
      (LinearMap.range (LocalizedModule.map (υ x).asIdeal.primeCompl (Q (ι x)).Pi₀)).restrictScalars (Localization.Away (f (ι x))) ⊔
        (υ x).asIdeal • (⊤ : Submodule (Localization.Away (f (ι x))) (stalk (Localization.Away (f (ι x))) (υ x) (Q (ι x)).T₁)) := by
    rw [← βι_ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x v]
    obtain ⟨r, hr, z, hz, hrz⟩ := Submodule.mem_sup.mp h
    rw [← hrz, map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr ⊢
      obtain ⟨a, rfl⟩ := hr
      exact ⟨βι₀ f Q T₀ p₀ ι υ hιυ x a,
        (βx_natural (Submonoid.powers (f (ι x))) T₀ (Q (ι x)).T₀
          (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
          (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
          T₁ (Q (ι x)).T₁ (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
          (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))) x (υ x) (hιυ x) Pi₀ (Q (ι x)).Pi₀
          (fun t => hPi₀ (ι x) t) a).symm⟩
    · have hz' : z ∈ ((PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x)).asIdeal • ⊤ :
          Submodule B (stalk B x T₁)) := by
        rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]; exact hz
      exact map_smul_top_le (υ x) (βι₁ f Q T₁ p₁ ι υ hιυ x).toLinearMap (Submodule.mem_map_of_mem hz')
  rw [eq_chart₀ f Q N₀g hN₀ ι υ hιυ x]
  exact (Q (ι x)).injective₁ (υ x) _ h'

include hN₀ ι υ hιυ hPi₀ in
theorem ug₀_locallyConstant (x : PrimeSpectrum B) (h : LinearMap.range Pi₀ ≤ x.asIdeal • (⊤ : Submodule B T₁)) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ x' ∈ U, LinearMap.range Pi₀ ≤ x'.asIdeal • (⊤ : Submodule B T₁) → N₀g x' = N₀g x := by
  have push : ∀ (y : PrimeSpectrum (Localization.Away (f (ι x)))),
      LinearMap.range Pi₀ ≤ (PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y).asIdeal • (⊤ : Submodule B T₁) →
      LinearMap.range (Q (ι x)).Pi₀ ≤ y.asIdeal • ⊤ := fun y hy =>
    range_le_smul_top_of_isLocalizedModule (f (ι x)) (p₀ (ι x)) (p₁ (ι x)) Pi₀ ((Q (ι x)).Pi₀) (hPi₀ (ι x)) y hy
  obtain ⟨U, hU, hxU, HU⟩ := (Q (ι x)).locallyConstant₀ (υ x)
    (push (υ x) (by rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]; exact h))
  refine ⟨PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) '' U,
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away (f (ι x))) (f (ι x))).isOpenMap _ hU,
    ⟨υ x, hxU, hιυ x⟩, ?_⟩
  rintro _ ⟨y, hyU, rfl⟩ hy
  rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y =
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y from rfl,
    hN₀ (ι x) y, HU y hyU (push y hy), eq_chart₀ f Q N₀g hN₀ ι υ hιυ x]

include hN₁ ι υ hιυ hPi₁ in
theorem ug₁_locallyConstant (x : PrimeSpectrum B) (h : LinearMap.range Pi₁ ≤ x.asIdeal • (⊤ : Submodule B T₀)) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ x' ∈ U, LinearMap.range Pi₁ ≤ x'.asIdeal • (⊤ : Submodule B T₀) → N₁g x' = N₁g x := by
  have push : ∀ (y : PrimeSpectrum (Localization.Away (f (ι x)))),
      LinearMap.range Pi₁ ≤ (PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y).asIdeal • (⊤ : Submodule B T₀) →
      LinearMap.range (Q (ι x)).Pi₁ ≤ y.asIdeal • ⊤ := fun y hy =>
    range_le_smul_top_of_isLocalizedModule (f (ι x)) (p₁ (ι x)) (p₀ (ι x)) Pi₁ ((Q (ι x)).Pi₁) (hPi₁ (ι x)) y hy
  obtain ⟨U, hU, hxU, HU⟩ := (Q (ι x)).locallyConstant₁ (υ x)
    (push (υ x) (by rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]; exact h))
  refine ⟨PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) '' U,
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away (f (ι x))) (f (ι x))).isOpenMap _ hU,
    ⟨υ x, hxU, hιυ x⟩, ?_⟩
  rintro _ ⟨y, hyU, rfl⟩ hy
  rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y =
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y from rfl,
    hN₁ (ι x) y, HU y hyU (push y hy), eq_chart₁ f Q N₁g hN₁ ι υ hιυ x]

end Fields2
end B24D

namespace B24D
section Fields3

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

variable (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀)
variable (hPi₀ : ∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) (hPi₁ : ∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t))

include hN₀ hN₁ hιυ in
theorem leg (x : PrimeSpectrum B) : N₀g x ≤ N₁g x := by
  rw [eq_chart₀ f Q N₀g hN₀ ι υ hιυ x, eq_chart₁ f Q N₁g hN₁ ι υ hιυ x]; exact (Q (ι x)).le (υ x)

include hN₀ hN₁ hιυ in
theorem smul_leg (x : PrimeSpectrum B) : ∀ v ∈ N₁g x, algebraMap 𝒪 K π • v ∈ N₀g x := by
  rw [eq_chart₀ f Q N₀g hN₀ ι υ hιυ x, eq_chart₁ f Q N₁g hN₁ ι υ hιυ x]; exact (Q (ι x)).smul_le (υ x)

include hPi₀ in
theorem ug_incl (x : PrimeSpectrum B) (w : latticeBaseChange 𝒪 K (locRing B x) (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) :
    ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x (inclBaseChange (locRing B x) (M' := (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (M := (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K))
        (leg f Q N₀g hN₀ N₁g hN₁ ι υ hιυ x) w) =
      LocalizedModule.map x.asIdeal.primeCompl Pi₀ (ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing B x) (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) = a • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [show inclBaseChange (locRing B x) (M' := (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (M := (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) (leg f Q N₀g hN₀ N₁g hN₁ ι υ hιυ x)
        ((1 : locRing B x) ⊗ₜ[𝒪] v) = (1 : locRing B x) ⊗ₜ[𝒪] Submodule.inclusion (leg f Q N₀g hN₀ N₁g hN₁ ι υ hιυ x) v
        from LinearMap.baseChange_tmul _ _ _,
      ug₁_tmul, ug₀_tmul, one_smul, one_smul]
    apply (βι₁ f Q T₁ p₁ ι υ hιυ x).injective
    rw [LinearEquiv.apply_symm_apply,
      βx_natural (Submonoid.powers (f (ι x))) T₀ (Q (ι x)).T₀ (τp (𝒪 := 𝒪) (A := (Localization.Away (f (ι x)))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
        (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))) T₁ (Q (ι x)).T₁
        (τp (𝒪 := 𝒪) (A := (Localization.Away (f (ι x)))) T₁ (Q (ι x)).T₁ (p₁ (ι x))) (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
        x (υ x) (hιυ x) Pi₀ (Q (ι x)).Pi₀ (fun t => hPi₀ (ι x) t)]
    show _ = LocalizedModule.map (υ x).asIdeal.primeCompl (Q (ι x)).Pi₀ (βι₀ f Q T₀ p₀ ι υ hιυ x ((βι₀ f Q T₀ p₀ ι υ hιυ x).symm _))
    rw [LinearEquiv.apply_symm_apply, ← (Q (ι x)).u₁_incl (υ x),
      show inclBaseChange (locRing (Localization.Away (f (ι x))) (υ x)) (M' := (Q (ι x)).L₀ (υ x)) (M := (Q (ι x)).L₁ (υ x)) ((Q (ι x)).le (υ x))
          ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] (⟨(v : Fin 2 → K), mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩ : ↥((Q (ι x)).N₀ (υ x)))) =
        (1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] Submodule.inclusion ((Q (ι x)).le (υ x)) ⟨(v : Fin 2 → K), mem_chart₀ f Q N₀g hN₀ ι υ hιυ x v.2⟩
        from LinearMap.baseChange_tmul _ _ _]
    rfl

include hPi₁ in
theorem ug_smul (x : PrimeSpectrum B) (w : latticeBaseChange 𝒪 K (locRing B x) (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) :
    ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x (((smulInto π (smul_leg f Q N₀g hN₀ N₁g hN₁ ι υ hιυ x)).baseChange (locRing B x) :
        latticeBaseChange 𝒪 K (locRing B x) (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K) →ₗ[locRing B x] latticeBaseChange 𝒪 K (locRing B x) (⟨N₀g x, full₀g f Q N₀g hN₀ ι υ hιυ x⟩ : FullLattice 𝒪 K)) w) =
      LocalizedModule.map x.asIdeal.primeCompl Pi₁ (ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing B x) (⟨N₁g x, full₁g f Q N₁g hN₁ ι υ hιυ x⟩ : FullLattice 𝒪 K)) = a • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [LinearMap.baseChange_tmul, ug₁_tmul, ug₀_tmul, one_smul, one_smul]
    apply (βι₀ f Q T₀ p₀ ι υ hιυ x).injective
    rw [LinearEquiv.apply_symm_apply,
      βx_natural (Submonoid.powers (f (ι x))) T₁ (Q (ι x)).T₁ (τp (𝒪 := 𝒪) (A := (Localization.Away (f (ι x)))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
        (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))) T₀ (Q (ι x)).T₀
        (τp (𝒪 := 𝒪) (A := (Localization.Away (f (ι x)))) T₀ (Q (ι x)).T₀ (p₀ (ι x))) (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
        x (υ x) (hιυ x) Pi₁ (Q (ι x)).Pi₁ (fun t => hPi₁ (ι x) t)]
    show _ = LocalizedModule.map (υ x).asIdeal.primeCompl (Q (ι x)).Pi₁ (βι₁ f Q T₁ p₁ ι υ hιυ x ((βι₁ f Q T₁ p₁ ι υ hιυ x).symm _))
    rw [LinearEquiv.apply_symm_apply, ← (Q (ι x)).u₀_smul (υ x), LinearMap.baseChange_tmul]
    rfl

end Fields3
end B24D

namespace B24D
section Cont

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

variable (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀)
variable (hPi₀ : ∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) (hPi₁ : ∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t))

variable (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
variable [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
variable [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
variable [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
variable [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
variable (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
variable [∀ i j, Module B (Q₂ i j).T₀] [∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₀]
variable [∀ i j, Module B (Q₂ i j).T₁] [∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₁]
variable (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
variable (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
variable (hc₀ : ∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t))
variable (hc₁ : ∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t))

theorem mem_pointUnder_iff {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
    (y : PrimeSpectrum A) (b : B) :
    b ∈ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B A) y).asIdeal ↔ algebraMap B A b ∈ y.asIdeal := Iff.rfl

include hN₀ hc₀ in
theorem ug₀_continuous (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ N₀g x) :
    ∃ (b : B) (t : T₀), b ∉ x.asIdeal ∧ ∀ (x' : PrimeSpectrum B) (hx' : b ∉ x'.asIdeal), ∃ hv' : v ∈ N₀g x',
      ug₀ f Q N₀g hN₀ T₀ p₀ ι υ hιυ x' ((1 : locRing B x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(N₀g x'))) =
        LocalizedModule.mk t ⟨b, hx'⟩ := by
  have hvy : v ∈ (Q (ι x)).N₀ (υ x) := mem_chart₀ f Q N₀g hN₀ ι υ hιυ x hv
  obtain ⟨c, t', hc, H⟩ := (Q (ι x)).u₀_continuous (υ x) v hvy

  obtain ⟨⟨b₀, ⟨_, a, rfl⟩⟩, hb₀⟩ := IsLocalization.surj (Submonoid.powers (f (ι x))) c
  obtain ⟨⟨t₀, ⟨_, e, rfl⟩⟩, ht₀⟩ := IsLocalizedModule.surj (Submonoid.powers (f (ι x))) (p₀ (ι x)) t'
  have hb₀' : c * algebraMap B (Localization.Away (f (ι x))) (f (ι x)) ^ a = algebraMap B _ b₀ := by
    simpa only [map_pow] using hb₀
  have ht₀' : f (ι x) ^ e • t' = p₀ (ι x) t₀ := by simpa only [Submonoid.smul_def] using ht₀
  clear hb₀ ht₀
  have hfx : f (ι x) ∉ x.asIdeal := not_mem_ι f ι υ hιυ x
  refine ⟨f (ι x) ^ (e + 1) * b₀, f (ι x) ^ (a + 1) • t₀, ?_, ?_⟩
  · intro hmem
    rcases x.isPrime.mem_or_mem hmem with h1 | h2
    · exact hfx (x.isPrime.mem_of_pow_mem _ h1)
    · have h3 : algebraMap B (Localization.Away (f (ι x))) b₀ ∈ (υ x).asIdeal := by
        rw [← mem_pointUnder_iff (𝒪 := 𝒪), hιυ x]; exact h2
      rw [← hb₀'] at h3
      rcases (υ x).isPrime.mem_or_mem h3 with h4 | h5
      · exact hc h4
      · exact (υ x).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h5
          ((IsLocalization.Away.algebraMap_isUnit (f (ι x))).pow a))
  · intro x' hx'
    have hfi : f (ι x) ∉ x'.asIdeal := fun h =>
      hx' (Ideal.mul_mem_right b₀ _ (Ideal.pow_mem_of_mem x'.asIdeal h (e + 1) e.succ_pos))
    have hb₀x' : b₀ ∉ x'.asIdeal := fun h => hx' (Ideal.mul_mem_left _ _ h)
    obtain ⟨y', hy'⟩ := exists_comap_eq (A := Localization.Away (f (ι x))) (f (ι x)) x' hfi
    have hy'' : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y' = x' := hy'
    have hcy' : c ∉ y'.asIdeal := by
      intro h
      apply hb₀x'
      have h' : algebraMap B _ b₀ ∈ y'.asIdeal := by rw [← hb₀']; exact Ideal.mul_mem_right _ _ h
      rwa [← mem_pointUnder_iff (𝒪 := 𝒪), hy''] at h'
    obtain ⟨hvy', Hy'⟩ := H y' hcy'
    have hv' : v ∈ N₀g x' := by rw [← hy'', hN₀]; exact hvy'
    refine ⟨hv', ?_⟩
    have key := chart₀ (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ)
      (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₀ := hc₀) x' (ι x) y' hy'' v hv' hvy'
    rw [Hy'] at key
    apply (βx (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) T₀ (Q (ι x)).T₀
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₀ (Q (ι x)).T₀ (p₀ (ι x)))
      (span_range_τp (f (ι x)) T₀ (Q (ι x)).T₀ (p₀ (ι x))) x' y' hy'').injective
    rw [← key, βx_mk, τp_apply, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def]
    rw [map_smul, ← ht₀', ← algebraMap_smul (Localization.Away (f (ι x))) (f (ι x) ^ (a + 1)),
      ← algebraMap_smul (Localization.Away (f (ι x))) (f (ι x) ^ e), smul_smul, smul_smul, map_mul, ← hb₀',
      map_pow, map_pow, map_pow]
    congr 1
    ring

include hN₁ hc₁ in
theorem ug₁_continuous (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ N₁g x) :
    ∃ (b : B) (t : T₁), b ∉ x.asIdeal ∧ ∀ (x' : PrimeSpectrum B) (hx' : b ∉ x'.asIdeal), ∃ hv' : v ∈ N₁g x',
      ug₁ f Q N₁g hN₁ T₁ p₁ ι υ hιυ x' ((1 : locRing B x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(N₁g x'))) =
        LocalizedModule.mk t ⟨b, hx'⟩ := by
  have hvy : v ∈ (Q (ι x)).N₁ (υ x) := mem_chart₁ f Q N₁g hN₁ ι υ hιυ x hv
  obtain ⟨c, t', hc, H⟩ := (Q (ι x)).u₁_continuous (υ x) v hvy

  obtain ⟨⟨b₀, ⟨_, a, rfl⟩⟩, hb₀⟩ := IsLocalization.surj (Submonoid.powers (f (ι x))) c
  obtain ⟨⟨t₀, ⟨_, e, rfl⟩⟩, ht₀⟩ := IsLocalizedModule.surj (Submonoid.powers (f (ι x))) (p₁ (ι x)) t'
  have hb₀' : c * algebraMap B (Localization.Away (f (ι x))) (f (ι x)) ^ a = algebraMap B _ b₀ := by
    simpa only [map_pow] using hb₀
  have ht₀' : f (ι x) ^ e • t' = p₁ (ι x) t₀ := by simpa only [Submonoid.smul_def] using ht₀
  clear hb₀ ht₀
  have hfx : f (ι x) ∉ x.asIdeal := not_mem_ι f ι υ hιυ x
  refine ⟨f (ι x) ^ (e + 1) * b₀, f (ι x) ^ (a + 1) • t₀, ?_, ?_⟩
  · intro hmem
    rcases x.isPrime.mem_or_mem hmem with h1 | h2
    · exact hfx (x.isPrime.mem_of_pow_mem _ h1)
    · have h3 : algebraMap B (Localization.Away (f (ι x))) b₀ ∈ (υ x).asIdeal := by
        rw [← mem_pointUnder_iff (𝒪 := 𝒪), hιυ x]; exact h2
      rw [← hb₀'] at h3
      rcases (υ x).isPrime.mem_or_mem h3 with h4 | h5
      · exact hc h4
      · exact (υ x).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h5
          ((IsLocalization.Away.algebraMap_isUnit (f (ι x))).pow a))
  · intro x' hx'
    have hfi : f (ι x) ∉ x'.asIdeal := fun h =>
      hx' (Ideal.mul_mem_right b₀ _ (Ideal.pow_mem_of_mem x'.asIdeal h (e + 1) e.succ_pos))
    have hb₀x' : b₀ ∉ x'.asIdeal := fun h => hx' (Ideal.mul_mem_left _ _ h)
    obtain ⟨y', hy'⟩ := exists_comap_eq (A := Localization.Away (f (ι x))) (f (ι x)) x' hfi
    have hy'' : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y' = x' := hy'
    have hcy' : c ∉ y'.asIdeal := by
      intro h
      apply hb₀x'
      have h' : algebraMap B _ b₀ ∈ y'.asIdeal := by rw [← hb₀']; exact Ideal.mul_mem_right _ _ h
      rwa [← mem_pointUnder_iff (𝒪 := 𝒪), hy''] at h'
    obtain ⟨hvy', Hy'⟩ := H y' hcy'
    have hv' : v ∈ N₁g x' := by rw [← hy'', hN₁]; exact hvy'
    refine ⟨hv', ?_⟩
    have key := chart₁ (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ)
      (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₁ := hc₁) x' (ι x) y' hy'' v hv' hvy'
    rw [Hy'] at key
    apply (βx (𝒪 := 𝒪) (Submonoid.powers (f (ι x))) T₁ (Q (ι x)).T₁
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) T₁ (Q (ι x)).T₁ (p₁ (ι x)))
      (span_range_τp (f (ι x)) T₁ (Q (ι x)).T₁ (p₁ (ι x))) x' y' hy'').injective
    rw [← key, βx_mk, τp_apply, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def]
    rw [map_smul, ← ht₀', ← algebraMap_smul (Localization.Away (f (ι x))) (f (ι x) ^ (a + 1)),
      ← algebraMap_smul (Localization.Away (f (ι x))) (f (ι x) ^ e), smul_smul, smul_smul, map_mul, ← hb₀',
      map_pow, map_pow, map_pow]
    congr 1
    ring

end Cont
end B24D

namespace B24D
section Datum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
variable (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
variable [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
variable [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁]
variable (N₀g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₀ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₀g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₀ y)
variable (N₁g : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K))
variable (hN₁ : ∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
  N₁g (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = (Q i).N₁ y)
variable (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀] [Module 𝒪 T₀] [IsScalarTower 𝒪 B T₀]
variable (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] [Module 𝒪 T₁] [IsScalarTower 𝒪 B T₁]
variable (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)]
variable (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)]
variable (ι : PrimeSpectrum B → Fin k) (υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x))))
variable (hιυ : ∀ x, DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

variable (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀)
variable (hPi₀ : ∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) (hPi₁ : ∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t))

variable (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
variable [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
variable [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
variable [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
variable [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
variable (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
variable [∀ i j, Module B (Q₂ i j).T₀] [∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₀]
variable [∀ i j, Module B (Q₂ i j).T₁] [∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₁]
variable (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
variable (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
variable (hc₀ : ∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t))
variable (hc₁ : ∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t))

variable (hO₀ : ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ N₀g x})
variable (hO₁ : ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ N₁g x})
variable (hP10 : ∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t) (hP01 : ∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t)

noncomputable def gluedDatum : DrinfeldDatum (K := K) π B where
  N₀ := N₀g
  N₁ := N₁g
  full₀ := fun x => full₀g (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (ι := ι) (υ := υ) (hιυ := hιυ) x
  full₁ := fun x => full₁g (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (ι := ι) (υ := υ) (hιυ := hιυ) x
  le := fun x => leg (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (ι := ι) (υ := υ) (hιυ := hιυ) x
  smul_le := fun x => smul_leg (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (ι := ι) (υ := υ) (hιυ := hιυ) x
  isOpen_setOf_mem₀ := hO₀
  isOpen_setOf_mem₁ := hO₁
  T₀ := T₀
  T₁ := T₁
  invertible₀ := inferInstance
  invertible₁ := inferInstance
  Pi₀ := Pi₀
  Pi₁ := Pi₁
  Pi₁_Pi₀ := hP10
  Pi₀_Pi₁ := hP01
  u₀ := fun x => ug₀ (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) x
  u₁ := fun x => ug₁ (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) x
  u₁_incl := fun x w => ug_incl (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁) (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₀ := Pi₀) (hPi₀ := hPi₀) x w
  u₀_smul := fun x w => ug_smul (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁) (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₁ := Pi₁) (hPi₁ := hPi₁) x w
  u₀_surjective := fun x => ug₀_surjective (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) x
  u₁_surjective := fun x => ug₁_surjective (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) x
  u₀_continuous := fun x v hv => ug₀_continuous (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₀ := hc₀) x v hv
  u₁_continuous := fun x v hv => ug₁_continuous (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₁ := hc₁) x v hv
  locallyConstant₀ := fun x h => ug₀_locallyConstant (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) (T₁ := T₁) (p₁ := p₁) (Pi₀ := Pi₀) (hPi₀ := hPi₀) x h
  locallyConstant₁ := fun x h => ug₁_locallyConstant (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (T₀ := T₀) (p₀ := p₀) (Pi₁ := Pi₁) (hPi₁ := hPi₁) x h
  injective₀ := fun x v h => ug₀_injective (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁) (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₁ := Pi₁) (hPi₁ := hPi₁) x v h
  injective₁ := fun x v h => ug₁_injective (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁) (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₀ := Pi₀) (hPi₀ := hPi₀) x v h
  hasDetIndex₀ := fun x h => ug₀_hasDetIndex (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) (T₁ := T₁) (p₁ := p₁) (Pi₀ := Pi₀) (hPi₀ := hPi₀) x h
  hasDetIndex₁ := fun x h => ug₁_hasDetIndex (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (T₀ := T₀) (p₀ := p₀) (Pi₁ := Pi₁) (hPi₁ := hPi₁) x h

noncomputable def gluedWitness (i : Fin k) :
    DrinfeldDatum.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))
      (gluedDatum (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁) (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₀ := Pi₀) (Pi₁ := Pi₁) (hPi₀ := hPi₀) (hPi₁ := hPi₁) (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₀ := hc₀) (hc₁ := hc₁)
        (hO₀ := hO₀) (hO₁ := hO₁) (hP10 := hP10) (hP01 := hP01)) (Q i) where
  N₀_eq := fun y => (hN₀ i y).symm
  N₁_eq := fun y => (hN₁ i y).symm
  τ₀ := τp (𝒪 := 𝒪) (A := Localization.Away (f i)) T₀ (Q i).T₀ (p₀ i)
  τ₁ := τp (𝒪 := 𝒪) (A := Localization.Away (f i)) T₁ (Q i).T₁ (p₁ i)
  span_range_τ₀ := span_range_τp (f i) T₀ (Q i).T₀ (p₀ i)
  span_range_τ₁ := span_range_τp (f i) T₁ (Q i).T₁ (p₁ i)
  τ₁_Pi₀ := fun t => hPi₀ i t
  τ₀_Pi₁ := fun t => hPi₁ i t
  u₀_eq := fun y v hv hv' t s hs H => by
    have key := chart₀ (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₀ := hc₀)
      (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) i y rfl v hv hv'
    have H' : ug₀ (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (T₀ := T₀) (p₀ := p₀) (ι := ι) (υ := υ) (hιυ := hιυ) (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y)
        ((1 : locRing B _) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₀g _))) = LocalizedModule.mk t ⟨s, hs⟩ := H
    rw [key, H']
    exact βx_mk (𝒪 := 𝒪) (Submonoid.powers (f i)) T₀ (Q i).T₀ (τp (𝒪 := 𝒪) (A := Localization.Away (f i)) T₀ (Q i).T₀ (p₀ i))
      (span_range_τp (f i) T₀ (Q i).T₀ (p₀ i)) _ y rfl t s hs
  u₁_eq := fun y v hv hv' t s hs H => by
    have key := chart₁ (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₁ := hc₁)
      (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) i y rfl v hv hv'
    have H' : ug₁ (f := f) (Q := Q) (N₁g := N₁g) (hN₁ := hN₁) (T₁ := T₁) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y)
        ((1 : locRing B _) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₁g _))) = LocalizedModule.mk t ⟨s, hs⟩ := H
    rw [key, H']
    exact βx_mk (𝒪 := 𝒪) (Submonoid.powers (f i)) T₁ (Q i).T₁ (τp (𝒪 := 𝒪) (A := Localization.Away (f i)) T₁ (Q i).T₁ (p₁ i))
      (span_range_τp (f i) T₁ (Q i).T₁ (p₁ i)) _ y rfl t s hs

end Datum
end B24D

open B24D in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
    [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
    [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
    (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
    (hl : ∀ i j : Fin k, (Q i).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (hr : ∀ i j : Fin k, (Q j).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j)) :
    ∃ Qg : DrinfeldDatum (K := K) π B,
      ∀ i : Fin k, Qg.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Q i) := by
  classical

  letI instQ₀ : ∀ i : Fin k, Module B (Q i).T₀ := fun i => Module.compHom _ (algebraMap B (Localization.Away (f i)))
  haveI : ∀ i : Fin k, IsScalarTower B (Localization.Away (f i)) (Q i).T₀ := fun i => ⟨fun b a t => by
    show (b • a) • t = algebraMap B (Localization.Away (f i)) b • (a • t); rw [Algebra.smul_def, mul_smul]⟩
  letI instQ₁ : ∀ i : Fin k, Module B (Q i).T₁ := fun i => Module.compHom _ (algebraMap B (Localization.Away (f i)))
  haveI : ∀ i : Fin k, IsScalarTower B (Localization.Away (f i)) (Q i).T₁ := fun i => ⟨fun b a t => by
    show (b • a) • t = algebraMap B (Localization.Away (f i)) b • (a • t); rw [Algebra.smul_def, mul_smul]⟩
  letI instQ₂₀ : ∀ i j : Fin k, Module B (Q₂ i j).T₀ := fun i j => Module.compHom _ (algebraMap B (C i j))
  haveI : ∀ i j : Fin k, IsScalarTower B (C i j) (Q₂ i j).T₀ := fun i j => ⟨fun b a t => by
    show (b • a) • t = algebraMap B (C i j) b • (a • t); rw [Algebra.smul_def, mul_smul]⟩
  letI instQ₂₁ : ∀ i j : Fin k, Module B (Q₂ i j).T₁ := fun i j => Module.compHom _ (algebraMap B (C i j))
  haveI : ∀ i j : Fin k, IsScalarTower B (C i j) (Q₂ i j).T₁ := fun i j => ⟨fun b a t => by
    show (b • a) • t = algebraMap B (C i j) b • (a • t); rw [Algebra.smul_def, mul_smul]⟩

  have Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j) :=
    fun i j => (hl i j).some
  have Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j) :=
    fun i j => (hr i j).some
  obtain ⟨T₀, T₁, _, _, _, _, _, _, Pi₀, Pi₁, p₀, p₁, hP10, hP01, hp₀, hp₁, hPi₀, hPi₁, hc₀, hc₁⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap f hf Q C Q₂ Wl Wr
  haveI : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i) := hp₀
  haveI : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i) := hp₁
  letI : Module 𝒪 T₀ := Module.compHom T₀ (algebraMap 𝒪 B)
  haveI : IsScalarTower 𝒪 B T₀ := ⟨fun r b t => by show (r • b) • t = algebraMap 𝒪 B r • (b • t); rw [Algebra.smul_def, mul_smul]⟩
  letI : Module 𝒪 T₁ := Module.compHom T₁ (algebraMap 𝒪 B)
  haveI : IsScalarTower 𝒪 B T₁ := ⟨fun r b t => by show (r • b) • t = algebraMap 𝒪 B r • (b • t); rw [Algebra.smul_def, mul_smul]⟩

  have hpt : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z →
      ∃ w : PrimeSpectrum (C i j),
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) w = y ∧
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) w = z := by
    intro i j y z hyz
    have hfi : f i ∉ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y).asIdeal := by
      have : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y ∈
          Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f i)))) := ⟨y, rfl⟩
      rwa [PrimeSpectrum.localization_away_comap_range _ (f i)] at this
    have hfj : f j ∉ (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y).asIdeal := by
      have : DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y ∈
          Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f j)))) := ⟨z, hyz.symm⟩
      rwa [PrimeSpectrum.localization_away_comap_range _ (f j)] at this
    obtain ⟨w, hw⟩ := exists_comap_eq (A := C i j) (f i * f j) _ (fun h => ((PrimeSpectrum.isPrime _).mem_or_mem h).elim hfi hfj)
    refine ⟨w, comap_injective (f i) ?_, comap_injective (f j) ?_⟩
    · rw [comap_pointUnder]; exact hw
    · rw [comap_pointUnder, hw]; exact hyz
  have compat₀ : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z → (Q i).N₀ y = (Q j).N₀ z := by
    intro i j y z hyz
    obtain ⟨w, hwy, hwz⟩ := hpt i j y z hyz
    rw [← hwy, ← hwz, ← (Wl i j).N₀_eq w, ← (Wr i j).N₀_eq w]
  have compat₁ : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z → (Q i).N₁ y = (Q j).N₁ z := by
    intro i j y z hyz
    obtain ⟨w, hwy, hwz⟩ := hpt i j y z hyz
    rw [← hwy, ← hwz, ← (Wl i j).N₁_eq w, ← (Wr i j).N₁_eq w]
  obtain ⟨N₀g, hN₀, hO₀⟩ := CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    f hf (fun i => (Q i).N₀) (fun i v => (Q i).isOpen_setOf_mem₀ v) compat₀
  obtain ⟨N₁g, hN₁, hO₁⟩ := CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    f hf (fun i => (Q i).N₁) (fun i v => (Q i).isOpen_setOf_mem₁ v) compat₁

  have cover : ∀ x : PrimeSpectrum B, ∃ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y = x := fun x => by
    obtain ⟨i, hi⟩ := exists_not_mem f hf x
    obtain ⟨y, hy⟩ := exists_comap_eq (A := Localization.Away (f i)) (f i) x hi
    exact ⟨i, y, hy⟩
  choose ι υ hιυ using cover
  exact ⟨gluedDatum (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁)
      (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₀ := Pi₀) (Pi₁ := Pi₁) (hPi₀ := hPi₀) (hPi₁ := hPi₁)
      (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₀ := hc₀) (hc₁ := hc₁) (hO₀ := hO₀) (hO₁ := hO₁) (hP10 := hP10) (hP01 := hP01),
    fun i => ⟨gluedWitness (f := f) (Q := Q) (N₀g := N₀g) (hN₀ := hN₀) (N₁g := N₁g) (hN₁ := hN₁) (T₀ := T₀) (T₁ := T₁)
      (p₀ := p₀) (p₁ := p₁) (ι := ι) (υ := υ) (hιυ := hιυ) (Pi₀ := Pi₀) (Pi₁ := Pi₁) (hPi₀ := hPi₀) (hPi₁ := hPi₁)
      (C := C) (Q₂ := Q₂) (Wl := Wl) (Wr := Wr) (hc₀ := hc₀) (hc₁ := hc₁) (hO₀ := hO₀) (hO₁ := hO₁) (hP10 := hP10) (hP01 := hP01) i⟩⟩

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap (solution)
