-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7b705f91-567f-5508-8ec8-31432bef69e4

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_IsLocalizedModule_exists_forall_isLocalizedModule_comp_eq_of_span_eq_top
import Theorems.Thm_Module_Invertible_of_isLocalizedModule_of_span_range_eq_top
import Theorems.Thm_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_comp
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_tau_unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B25TG

open CerednikDrinfeld.FormalOmega.DrinfeldDatum

section Rings

variable {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S] {T : Type} [CommRing T] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

theorem away_cancel (x y : R) [IsLocalization.Away x S] [IsLocalization.Away (x * y) T] :
    IsLocalization.Away (algebraMap R S y) T := by
  have hle : Submonoid.powers (x * y) ≤ Submonoid.powers x ⊔ Submonoid.powers y := by
    rintro _ ⟨n, rfl⟩
    show (x * y) ^ n ∈ _
    rw [mul_pow]
    exact Submonoid.mem_sup.mpr ⟨_, ⟨n, rfl⟩, _, ⟨n, rfl⟩, rfl⟩
  haveI h1 : IsLocalization (Submonoid.powers x ⊔ Submonoid.powers y) T := by
    refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (x * y)) _ hle ?_
    intro n hn
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hn
    refine ⟨(x * y) ^ (a + b), ⟨a + b, rfl⟩, ?_⟩
    rw [mul_pow, pow_add, pow_add]
    exact mul_dvd_mul (Dvd.intro _ rfl) (Dvd.intro_left _ rfl)
  have h2 : IsLocalization ((Submonoid.powers x ⊔ Submonoid.powers y).map (algebraMap R S)) T :=
    IsLocalization.isLocalization_of_submonoid_le S T (Submonoid.powers x) _ le_sup_left
  have hle' : Submonoid.powers (algebraMap R S y) ≤ (Submonoid.powers x ⊔ Submonoid.powers y).map (algebraMap R S) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨y ^ n, Submonoid.mem_sup.mpr ⟨1, ⟨0, (pow_zero x)⟩, _, ⟨n, rfl⟩, one_mul _⟩, map_pow _ _ _⟩
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (algebraMap R S y)) _ hle' ?_).mpr h2
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hm
  refine ⟨algebraMap R S y ^ b, ⟨b, rfl⟩, ?_⟩
  rw [map_mul, map_pow, map_pow]
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := S) x).pow a
  exact ⟨↑u⁻¹, by rw [← hu, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

end Rings

end B25TG

namespace B25TG

section Restrict

variable {B : Type} [CommRing B] {A : Type} [CommRing A] [Algebra B A]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower B A N]

theorem isLocalizedModule_restrictScalars (S : Submonoid B) (g : M →ₗ[A] N)
    [h : IsLocalizedModule (S.map (algebraMap B A)) g] : IsLocalizedModule S (g.restrictScalars B) where
  map_units s := by
    have hu := h.map_units ⟨algebraMap B A s, s, s.2, rfl⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    have heq : ∀ n : N, (algebraMap B (Module.End B N) ↑s) n = (algebraMap A (Module.End A N) (algebraMap B A ↑s)) n :=
      fun n => by simp only [Module.algebraMap_end_apply, algebraMap_smul]
    exact ⟨fun a b hab => hu.1 (by rw [← heq, ← heq]; exact hab), fun n => by
      obtain ⟨m, hm⟩ := hu.2 n; exact ⟨m, by rw [heq]; exact hm⟩⟩
  surj n := by
    obtain ⟨⟨m, ⟨_, s, hs, rfl⟩⟩, e⟩ := h.surj n
    exact ⟨⟨m, ⟨s, hs⟩⟩, by simpa only [Submonoid.smul_def, algebraMap_smul, LinearMap.restrictScalars_apply] using e⟩
  exists_of_eq {m m'} e := by
    obtain ⟨⟨_, s, hs, rfl⟩, hc⟩ := h.exists_of_eq (by simpa only [LinearMap.restrictScalars_apply] using e)
    exact ⟨⟨s, hs⟩, by simpa only [Submonoid.smul_def, algebraMap_smul] using hc⟩

end Restrict

section SemilinearGen

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]

def linB (φ : A →ₐ[𝒪] C) (hφ : ∀ b, φ (algebraMap B A b) = algebraMap B C b) (τ : M →ₛₗ[(φ : A →+* C)] N) :
    M →ₗ[B] N where
  toFun := τ
  map_add' a b := map_add τ a b
  map_smul' b m := by
    rw [← algebraMap_smul A b m, LinearMap.map_smulₛₗ]
    show φ (algebraMap B A b) • τ m = b • τ m
    rw [hφ, algebraMap_smul]

theorem linB_apply (φ : A →ₐ[𝒪] C) (hφ : ∀ b, φ (algebraMap B A b) = algebraMap B C b)
    (τ : M →ₛₗ[(φ : A →+* C)] N) (m : M) : linB φ hφ τ m = τ m := rfl

end SemilinearGen

section Semilinear

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [Algebra A C] [IsScalarTower 𝒪 A C] [IsScalarTower B A C]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]

theorem toAlgHom_algebraMap (b : B) : (IsScalarTower.toAlgHom 𝒪 A C) (algebraMap B A b) = algebraMap B C b :=
  (IsScalarTower.algebraMap_apply B A C b).symm

theorem isLocalizedModule_linB (y : B) [IsLocalization.Away (algebraMap B A y) C]
    [Module.Invertible A M] [Module.Invertible C N]
    (τ : M →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] N) (hτ : Submodule.span C (Set.range τ) = ⊤) :
    IsLocalizedModule (Submonoid.powers y) (linB (IsScalarTower.toAlgHom 𝒪 A C) toAlgHom_algebraMap τ) := by
  letI : Module A N := Module.compHom N (algebraMap A C)
  haveI : IsScalarTower A C N := ⟨fun a c n => by
    show (a • c) • n = (algebraMap A C a) • (c • n); rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower B A N := ⟨fun b a n => by
    show (algebraMap A C (b • a)) • n = b • ((algebraMap A C a) • n)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]⟩
  let τA : M →ₗ[A] N :=
    { toFun := τ
      map_add' := fun a b => map_add τ a b
      map_smul' := fun a m => by rw [LinearMap.map_smulₛₗ]; rfl }
  have hsurj : Function.Surjective (τA.liftBaseChange C) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← hτ]
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  have hbc : IsBaseChange C τA :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hsurj))
      (fun t => by rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul])
  haveI hA : IsLocalizedModule (Submonoid.powers (algebraMap B A y)) τA :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap B A y)) C τA).mpr hbc
  haveI : IsLocalizedModule ((Submonoid.powers y).map (algebraMap B A)) τA := by
    rw [Submonoid.map_powers]; exact hA
  have key := isLocalizedModule_restrictScalars (Submonoid.powers y) τA
  have heq : τA.restrictScalars B = linB (IsScalarTower.toAlgHom 𝒪 A C) toAlgHom_algebraMap τ :=
    LinearMap.ext fun _ => rfl
  rwa [heq] at key

end Semilinear

end B25TG

namespace B25TG

open CerednikDrinfeld.FormalOmega.DrinfeldDatum

section Witness

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}

theorem tau_eq_of_eq {A : Type} [CommRing A] [Algebra 𝒪 A] {D : Type} [CommRing D] [Algebra 𝒪 D]
    {g g' : A →ₐ[𝒪] D} (hg : g = g') {Q : DrinfeldDatum (K := K) π A} {Q' : DrinfeldDatum (K := K) π D}
    (W : Q.BaseChangeAlong g Q') (W' : Q.BaseChangeAlong g' Q') :
    (∀ t, W.τ₀ t = W'.τ₀ t) ∧ (∀ t, W.τ₁ t = W'.τ₁ t) := by
  subst hg
  exact CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.tau_unique g W W'

def castAlong {A : Type} [CommRing A] [Algebra 𝒪 A] {D : Type} [CommRing D] [Algebra 𝒪 D]
    {g g' : A →ₐ[𝒪] D} (hg : g = g') {Q : DrinfeldDatum (K := K) π A} {Q' : DrinfeldDatum (K := K) π D}
    (W : Q.BaseChangeAlong g Q') : Q.BaseChangeAlong g' Q' := hg ▸ W

theorem comp_eq_comp {A : Type} [CommRing A] [Algebra 𝒪 A] {C₁ : Type} [CommRing C₁] [Algebra 𝒪 C₁]
    {C₂ : Type} [CommRing C₂] [Algebra 𝒪 C₂] {D : Type} [CommRing D] [Algebra 𝒪 D]
    (ga : A →ₐ[𝒪] C₁) (ha : C₁ →ₐ[𝒪] D) (gb : A →ₐ[𝒪] C₂) (hb : C₂ →ₐ[𝒪] D) (heq : ha.comp ga = hb.comp gb)
    {Q : DrinfeldDatum (K := K) π A} {Qa : DrinfeldDatum (K := K) π C₁} {Qb : DrinfeldDatum (K := K) π C₂}
    {Q₃ : DrinfeldDatum (K := K) π D}
    (Wa : Q.BaseChangeAlong ga Qa) (Wa' : Qa.BaseChangeAlong ha Q₃)
    (Wb : Q.BaseChangeAlong gb Qb) (Wb' : Qb.BaseChangeAlong hb Q₃) :
    (∀ t, Wa'.τ₀ (Wa.τ₀ t) = Wb'.τ₀ (Wb.τ₀ t)) ∧ (∀ t, Wa'.τ₁ (Wa.τ₁ t) = Wb'.τ₁ (Wb.τ₁ t)) := by
  obtain ⟨Wca, hca₀, hca₁⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp ga ha Wa Wa'
  obtain ⟨Wcb, hcb₀, hcb₁⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp gb hb Wb Wb'
  obtain ⟨h₀, h₁⟩ := tau_eq_of_eq heq Wca Wcb
  exact ⟨fun t => by rw [← hca₀, h₀, hcb₀], fun t => by rw [← hca₁, h₁, hcb₁]⟩

end Witness

section Lift

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem algHom_ext_of_isLocalization (S : Submonoid B) {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
    [IsScalarTower 𝒪 B A] [IsLocalization S A] {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra B D]
    (φ ψ : A →ₐ[𝒪] D) (hφ : ∀ b, φ (algebraMap B A b) = algebraMap B D b)
    (hψ : ∀ b, ψ (algebraMap B A b) = algebraMap B D b) : φ = ψ := by
  have h : (φ : A →+* D) = (ψ : A →+* D) :=
    IsLocalization.ringHom_ext S (RingHom.ext fun b => by simp [hφ, hψ])
  exact AlgHom.ext fun a => RingHom.congr_fun h a

noncomputable def liftAlgHom (x : B) {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
    [IsLocalization.Away x A] {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra B D] [IsScalarTower 𝒪 B D]
    (hx : IsUnit (algebraMap B D x)) : A →ₐ[𝒪] D :=
  { IsLocalization.Away.lift x hx with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply 𝒪 B A, IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply] }

theorem liftAlgHom_algebraMap (x : B) {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
    [IsLocalization.Away x A] {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra B D] [IsScalarTower 𝒪 B D]
    (hx : IsUnit (algebraMap B D x)) (b : B) : liftAlgHom (𝒪 := 𝒪) x hx (algebraMap B A b) = algebraMap B D b :=
  IsLocalization.Away.lift_eq x hx b

end Lift

end B25TG

namespace B25TG

open CerednikDrinfeld.FormalOmega.DrinfeldDatum

section Triple

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
  {C₁ : Type} [CommRing C₁] [Algebra 𝒪 C₁] [Algebra B C₁] [IsScalarTower 𝒪 B C₁] [Algebra A C₁]
  [IsScalarTower B A C₁] [IsScalarTower 𝒪 A C₁]
  {C₂ : Type} [CommRing C₂] [Algebra 𝒪 C₂] [Algebra B C₂] [Algebra A C₂] [IsScalarTower B A C₂] [IsScalarTower 𝒪 A C₂]
  {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra B D] [IsScalarTower 𝒪 B D] [Algebra C₂ D] [IsScalarTower B C₂ D]
  [IsScalarTower 𝒪 C₂ D]

theorem comp_eq_of_isLocalization (S : Submonoid B) [IsLocalization S A] (h : C₁ →ₐ[𝒪] D)
    (hh : ∀ b, h (algebraMap B C₁ b) = algebraMap B D b) :
    h.comp (IsScalarTower.toAlgHom 𝒪 A C₁) = (IsScalarTower.toAlgHom 𝒪 C₂ D).comp (IsScalarTower.toAlgHom 𝒪 A C₂) := by
  apply algHom_ext_of_isLocalization S
  · intro b
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply B A C₁ b, hh]
  · intro b
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply,
      ← IsScalarTower.algebraMap_apply B A C₂ b, ← IsScalarTower.algebraMap_apply B C₂ D b]

theorem nonempty_witness_lift (S : Submonoid B) [IsLocalization S A] (x y : B) [IsLocalization.Away x C₁]
    [IsLocalization.Away (x * y) D] (h : C₁ →ₐ[𝒪] D) (hh : ∀ b, h (algebraMap B C₁ b) = algebraMap B D b)
    {Q : DrinfeldDatum (K := K) π A} {Q₁ : DrinfeldDatum (K := K) π C₁} {Q₂ : DrinfeldDatum (K := K) π C₂}
    {Q₃ : DrinfeldDatum (K := K) π D}
    (Wa : Q.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 A C₁) Q₁)
    (Wb : Q.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 A C₂) Q₂)
    (Wc : Q₂.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 C₂ D) Q₃) :
    Nonempty (Q₁.BaseChangeAlong h Q₃) := by
  letI alg : Algebra C₁ D := (h : C₁ →+* D).toAlgebra
  haveI : IsScalarTower B C₁ D := IsScalarTower.of_algebraMap_eq (fun b => (hh b).symm)
  haveI : IsScalarTower 𝒪 C₁ D := IsScalarTower.of_algebraMap_eq (fun r => (h.commutes r).symm)
  haveI : IsLocalization.Away (algebraMap B C₁ y) D := away_cancel x y
  obtain ⟨Q₃', hQ₃'⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization Q₁
    (Submonoid.powers (algebraMap B C₁ y)) D
  have hta : IsScalarTower.toAlgHom 𝒪 C₁ D = h := AlgHom.ext fun _ => rfl
  let Wd : Q₁.BaseChangeAlong h Q₃' := castAlong hta hQ₃'.some
  obtain ⟨Wb3, -, -⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp _ _ Wb Wc
  obtain ⟨Wa3, -, -⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp _ _ Wa Wd
  have hm := comp_eq_of_isLocalization (A := A) (C₂ := C₂) S h hh
  obtain ⟨e, -, -⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_iso _ (castAlong hm Wa3) Wb3
  exact CerednikDrinfeld.FormalOmega.DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic h ⟨Wd⟩ ⟨e⟩

end Triple

end B25TG

namespace B25TG

theorem piGlue
    {B : Type} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤) (c : B)
    (M0 M1 : Fin k → Type) [∀ i, AddCommGroup (M0 i)] [∀ i, Module B (M0 i)] [∀ i, AddCommGroup (M1 i)] [∀ i, Module B (M1 i)]
    (X0 X1 : Fin k → Fin k → Type) [∀ i j, AddCommGroup (X0 i j)] [∀ i j, Module B (X0 i j)]
    [∀ i j, AddCommGroup (X1 i j)] [∀ i j, Module B (X1 i j)]
    (ρl0 : ∀ i j, M0 i →ₗ[B] X0 i j) (ρr0 : ∀ i j, M0 j →ₗ[B] X0 i j)
    (ρl1 : ∀ i j, M1 i →ₗ[B] X1 i j) (ρr1 : ∀ i j, M1 j →ₗ[B] X1 i j)
    (hρr0 : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr0 i j))
    (hρr1 : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr1 i j))
    (N0 N1 : Type) [AddCommGroup N0] [Module B N0] [AddCommGroup N1] [Module B N1]
    (p0 : ∀ i, N0 →ₗ[B] M0 i) (p1 : ∀ i, N1 →ₗ[B] M1 i)
    (hp0 : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p0 i))
    (hp1 : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p1 i))
    (hp0c : ∀ i j, ρl0 i j ∘ₗ p0 i = ρr0 i j ∘ₗ p0 j) (hp1c : ∀ i j, ρl1 i j ∘ₗ p1 i = ρr1 i j ∘ₗ p1 j)

    (P0 : ∀ i, M0 i →ₗ[B] M1 i) (P1 : ∀ i, M1 i →ₗ[B] M0 i)
    (hP10 : ∀ i m, P1 i (P0 i m) = c • m) (hP01 : ∀ i m, P0 i (P1 i m) = c • m)
    (Y0 : ∀ i j, X0 i j →ₗ[B] X1 i j) (Y1 : ∀ i j, X1 i j →ₗ[B] X0 i j)
    (hl0 : ∀ i j m, ρl1 i j (P0 i m) = Y0 i j (ρl0 i j m)) (hr0 : ∀ i j m, ρr1 i j (P0 j m) = Y0 i j (ρr0 i j m))
    (hl1 : ∀ i j m, ρl0 i j (P1 i m) = Y1 i j (ρl1 i j m)) (hr1 : ∀ i j m, ρr0 i j (P1 j m) = Y1 i j (ρr1 i j m)) :
    ∃ (Pi0 : N0 →ₗ[B] N1) (Pi1 : N1 →ₗ[B] N0),
      (∀ i t, p1 i (Pi0 t) = P0 i (p0 i t)) ∧ (∀ i t, p0 i (Pi1 t) = P1 i (p1 i t)) ∧
      (∀ t, Pi1 (Pi0 t) = c • t) ∧ (∀ t, Pi0 (Pi1 t) = c • t) := by

  have hg0 : ∀ i j, ρl1 i j ∘ₗ (P0 i ∘ₗ p0 i) = ρr1 i j ∘ₗ (P0 j ∘ₗ p0 j) := by
    intro i j
    ext t
    simp only [LinearMap.comp_apply]
    rw [hl0, hr0, ← LinearMap.comp_apply (ρl0 i j), hp0c, LinearMap.comp_apply]
  obtain ⟨Pi0, hPi0, -⟩ := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M1 X1 ρl1 ρr1 hρr1
    N1 p1 hp1 hp1c N0 (fun i => P0 i ∘ₗ p0 i) hg0

  have hg1 : ∀ i j, ρl0 i j ∘ₗ (P1 i ∘ₗ p1 i) = ρr0 i j ∘ₗ (P1 j ∘ₗ p1 j) := by
    intro i j
    ext t
    simp only [LinearMap.comp_apply]
    rw [hl1, hr1, ← LinearMap.comp_apply (ρl1 i j), hp1c, LinearMap.comp_apply]
  obtain ⟨Pi1, hPi1, -⟩ := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M0 X0 ρl0 ρr0 hρr0
    N0 p0 hp0 hp0c N1 (fun i => P1 i ∘ₗ p1 i) hg1
  have hPi0' : ∀ i t, p1 i (Pi0 t) = P0 i (p0 i t) := fun i t => by
    have := congrArg (fun F : N0 →ₗ[B] M1 i => F t) (hPi0 i); simpa using this
  have hPi1' : ∀ i t, p0 i (Pi1 t) = P1 i (p1 i t) := fun i t => by
    have := congrArg (fun F : N1 →ₗ[B] M0 i => F t) (hPi1 i); simpa using this
  refine ⟨Pi0, Pi1, hPi0', hPi1', ?_, ?_⟩
  ·
    have hgc : ∀ i j, ρl0 i j ∘ₗ (c • p0 i) = ρr0 i j ∘ₗ (c • p0 j) := by
      intro i j
      rw [LinearMap.comp_smul, LinearMap.comp_smul, hp0c]
    have U0 := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M0 X0 ρl0 ρr0 hρr0
      N0 p0 hp0 hp0c N0 (fun i => c • p0 i) hgc
    have h1 : ∀ i, p0 i ∘ₗ (Pi1 ∘ₗ Pi0) = c • p0 i := by
      intro i; ext t
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hPi1', hPi0', hP10]
    have h2 : ∀ i, p0 i ∘ₗ (c • (LinearMap.id : N0 →ₗ[B] N0)) = c • p0 i := by
      intro i; rw [LinearMap.comp_smul, LinearMap.comp_id]
    have heq := U0.unique h1 h2
    intro t
    have := congrArg (fun F : N0 →ₗ[B] N0 => F t) heq
    simpa using this
  ·
    have hgc : ∀ i j, ρl1 i j ∘ₗ (c • p1 i) = ρr1 i j ∘ₗ (c • p1 j) := by
      intro i j
      rw [LinearMap.comp_smul, LinearMap.comp_smul, hp1c]
    have U1 := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M1 X1 ρl1 ρr1 hρr1
      N1 p1 hp1 hp1c N1 (fun i => c • p1 i) hgc
    have h1 : ∀ i, p1 i ∘ₗ (Pi0 ∘ₗ Pi1) = c • p1 i := by
      intro i; ext t
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hPi0', hPi1', hP01]
    have h2 : ∀ i, p1 i ∘ₗ (c • (LinearMap.id : N1 →ₗ[B] N1)) = c • p1 i := by
      intro i; rw [LinearMap.comp_smul, LinearMap.comp_id]
    have heq := U1.unique h1 h2
    intro t
    have := congrArg (fun F : N1 →ₗ[B] N1 => F t) heq
    simpa using this

end B25TG

namespace B25TG

abbrev D3 {B : Type} [CommRing B] {k : ℕ} (f : Fin k → B) (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)]
    [∀ i j, Algebra B (C i j)] (i j l : Fin k) : Type :=
  Localization.Away (algebraMap B (C j l) (f i))

end B25TG

open B25TG CerednikDrinfeld.FormalOmega.DrinfeldDatum in
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
    (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
    [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
    [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁] :
    ∃ (T₀ T₁ : Type) (_ : AddCommGroup T₀) (_ : AddCommGroup T₁) (_ : Module B T₀) (_ : Module B T₁)
      (_ : Module.Invertible B T₀) (_ : Module.Invertible B T₁)
      (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀) (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁),
      (∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t) ∧ (∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)) ∧
      (∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) ∧ (∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t)) ∧
      (∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t)) ∧
      (∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t)) := by
  classical

  letI mC₀ : ∀ i j, Module B (Q₂ i j).T₀ := fun i j => Module.compHom _ (algebraMap B (C i j))
  haveI tC₀ : ∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₀ := fun i j => ⟨fun b c t => by
    show (b • c) • t = algebraMap B (C i j) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  letI mC₁ : ∀ i j, Module B (Q₂ i j).T₁ := fun i j => Module.compHom _ (algebraMap B (C i j))
  haveI tC₁ : ∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₁ := fun i j => ⟨fun b c t => by
    show (b • c) • t = algebraMap B (C i j) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩

  have ex3 : ∀ i j l : Fin k, ∃ Q₃ : DrinfeldDatum (K := K) π (D3 f C i j l),
      (Q₂ j l).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)) Q₃ := fun i j l =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization (Q₂ j l)
      (Submonoid.powers (algebraMap B (C j l) (f i))) (D3 f C i j l)
  choose Q₃ hQ₃ using ex3
  let W₃ : ∀ i j l, (Q₂ j l).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)) (Q₃ i j l) :=
    fun i j l => (hQ₃ i j l).some
  letI mD₀ : ∀ i j l, Module B (Q₃ i j l).T₀ := fun i j l => Module.compHom _ (algebraMap B (D3 f C i j l))
  haveI tD₀ : ∀ i j l, IsScalarTower B (D3 f C i j l) (Q₃ i j l).T₀ := fun i j l => ⟨fun b c t => by
    show (b • c) • t = algebraMap B (D3 f C i j l) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  letI mD₁ : ∀ i j l, Module B (Q₃ i j l).T₁ := fun i j l => Module.compHom _ (algebraMap B (D3 f C i j l))
  haveI tD₁ : ∀ i j l, IsScalarTower B (D3 f C i j l) (Q₃ i j l).T₁ := fun i j l => ⟨fun b c t => by
    show (b • c) • t = algebraMap B (D3 f C i j l) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩

  have huC : ∀ i j, IsUnit (algebraMap B (C i j) (f i)) ∧ IsUnit (algebraMap B (C i j) (f j)) := fun i j =>
    ⟨IsLocalization.Away.isUnit_of_dvd (f i * f j) (Dvd.intro _ rfl),
     IsLocalization.Away.isUnit_of_dvd (f i * f j) (Dvd.intro_left _ rfl)⟩
  have huD : ∀ i j l (b : B), IsUnit (algebraMap B (C j l) b) → IsUnit (algebraMap B (D3 f C i j l) b) :=
    fun i j l b hb => by rw [IsScalarTower.algebraMap_apply B (C j l) (D3 f C i j l)]; exact hb.map _
  have hui : ∀ i j l, IsUnit (algebraMap B (D3 f C i j l) (f i)) := fun i j l => by
    rw [IsScalarTower.algebraMap_apply B (C j l) (D3 f C i j l)]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap B (C j l) (f i))
  have hu1 : ∀ i j l, IsUnit (algebraMap B (D3 f C i j l) (f i * f j)) := fun i j l => by
    rw [map_mul]; exact (hui i j l).mul (huD i j l _ (huC j l).1)
  have hu2 : ∀ i j l, IsUnit (algebraMap B (D3 f C i j l) (f i * f l)) := fun i j l => by
    rw [map_mul]; exact (hui i j l).mul (huD i j l _ (huC j l).2)
  let h1 : ∀ i j l, C i j →ₐ[𝒪] D3 f C i j l := fun i j l => liftAlgHom (f i * f j) (hu1 i j l)
  let h2 : ∀ i j l, C i l →ₐ[𝒪] D3 f C i j l := fun i j l => liftAlgHom (f i * f l) (hu2 i j l)
  have hh1 : ∀ i j l (b : B), h1 i j l (algebraMap B (C i j) b) = algebraMap B (D3 f C i j l) b :=
    fun i j l b => liftAlgHom_algebraMap (f i * f j) (hu1 i j l) b
  have hh2 : ∀ i j l (b : B), h2 i j l (algebraMap B (C i l) b) = algebraMap B (D3 f C i j l) b :=
    fun i j l b => liftAlgHom_algebraMap (f i * f l) (hu2 i j l) b

  haveI aw0 : ∀ i j l, IsLocalization.Away (f i * (f j * f l)) (D3 f C i j l) := fun i j l =>
    IsLocalization.Away.mul (C j l) (D3 f C i j l) (f j * f l) (f i)
  haveI aw1 : ∀ i j l, IsLocalization.Away (f i * f j * f l) (D3 f C i j l) := fun i j l => by
    rw [mul_assoc]; exact aw0 i j l
  haveI aw2 : ∀ i j l, IsLocalization.Away (f i * f l * f j) (D3 f C i j l) := fun i j l => by
    rw [mul_assoc, mul_comm (f l)]; exact aw0 i j l

  have hW₁ : ∀ i j l, Nonempty ((Q₂ i j).BaseChangeAlong (h1 i j l) (Q₃ i j l)) := fun i j l =>
    nonempty_witness_lift (A := Localization.Away (f j)) (Submonoid.powers (f j)) (f i * f j) (f l) (h1 i j l)
      (hh1 i j l) (Wr i j) (Wl j l) (W₃ i j l)
  have hW₂ : ∀ i j l, Nonempty ((Q₂ i l).BaseChangeAlong (h2 i j l) (Q₃ i j l)) := fun i j l =>
    nonempty_witness_lift (A := Localization.Away (f l)) (Submonoid.powers (f l)) (f i * f l) (f j) (h2 i j l)
      (hh2 i j l) (Wr i l) (Wr j l) (W₃ i j l)
  let W₁ : ∀ i j l, (Q₂ i j).BaseChangeAlong (h1 i j l) (Q₃ i j l) := fun i j l => (hW₁ i j l).some
  let W₂ : ∀ i j l, (Q₂ i l).BaseChangeAlong (h2 i j l) (Q₃ i j l) := fun i j l => (hW₂ i j l).some

  have hm1 : ∀ i j l, (h1 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) =
      (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C j l)) :=
    fun i j l => comp_eq_of_isLocalization (Submonoid.powers (f j)) (h1 i j l) (hh1 i j l)
  have hm2 : ∀ i j l, (h2 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f l)) (C i l)) =
      (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f l)) (C j l)) :=
    fun i j l => comp_eq_of_isLocalization (Submonoid.powers (f l)) (h2 i j l) (hh2 i j l)
  have hm12 : ∀ i j l, (h1 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) =
      (h2 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i l)) := fun i j l => by
    apply algHom_ext_of_isLocalization (Submonoid.powers (f i))
    · intro b; rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply B _ (C i j) b, hh1]
    · intro b; rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply B _ (C i l) b, hh2]

  let ρl₀ : ∀ i j, (Q i).T₀ →ₗ[B] (Q₂ i j).T₀ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wl i j).τ₀
  let ρr₀ : ∀ i j, (Q j).T₀ →ₗ[B] (Q₂ i j).T₀ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wr i j).τ₀
  have hρr₀ : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr₀ i j) := fun i j => by
    haveI : IsLocalization.Away (f j * f i) (C i j) := by rw [mul_comm]; infer_instance
    haveI : IsLocalization.Away (algebraMap B (Localization.Away (f j)) (f i)) (C i j) := away_cancel (f j) (f i)
    exact isLocalizedModule_linB (f i) (Wr i j).τ₀ (Wr i j).span_range_τ₀
  let σ₃₀ : ∀ i j l, (Q₂ j l).T₀ →ₗ[B] (Q₃ i j l).T₀ := fun i j l =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (W₃ i j l).τ₀
  have hσ₃₀ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃₀ i j l) := fun i j l =>
    isLocalizedModule_linB (f i) (W₃ i j l).τ₀ (W₃ i j l).span_range_τ₀
  let σ₁₀ : ∀ i j l, (Q₂ i j).T₀ →ₗ[B] (Q₃ i j l).T₀ := fun i j l => linB (h1 i j l) (hh1 i j l) (W₁ i j l).τ₀
  let σ₂₀ : ∀ i j l, (Q₂ i l).T₀ →ₗ[B] (Q₃ i j l).T₀ := fun i j l => linB (h2 i j l) (hh2 i j l) (W₂ i j l).τ₀
  have towBl : ∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j) := fun i j => inferInstance
  have towBr : ∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j) := fun i j => inferInstance
  have hdiag₀ : ∀ i, ρl₀ i i = ρr₀ i i := fun i => by
    apply LinearMap.ext; intro t
    refine (tau_eq_of_eq ?_ (Wl i i) (Wr i i)).1 t
    apply algHom_ext_of_isLocalization (Submonoid.powers (f i))
    · intro b; exact (@IsScalarTower.algebraMap_apply B _ _ _ _ _ _ (_) _ (towBl i i) b).symm
    · intro b; exact (@IsScalarTower.algebraMap_apply B _ _ _ _ _ _ (_) _ (towBr i i) b).symm
  have hcoc₁₀ : ∀ i j l, σ₁₀ i j l ∘ₗ ρl₀ i j = σ₂₀ i j l ∘ₗ ρl₀ i l := fun i j l =>
    LinearMap.ext fun t => (comp_eq_comp _ _ _ _ (hm12 i j l) (Wl i j) (W₁ i j l) (Wl i l) (W₂ i j l)).1 t
  have hcoc₂₀ : ∀ i j l, σ₁₀ i j l ∘ₗ ρr₀ i j = σ₃₀ i j l ∘ₗ ρl₀ j l := fun i j l =>
    LinearMap.ext fun t => (comp_eq_comp _ _ _ _ (hm1 i j l) (Wr i j) (W₁ i j l) (Wl j l) (W₃ i j l)).1 t
  have hcoc₃₀ : ∀ i j l, σ₂₀ i j l ∘ₗ ρr₀ i l = σ₃₀ i j l ∘ₗ ρr₀ j l := fun i j l =>
    LinearMap.ext fun t => (comp_eq_comp _ _ _ _ (hm2 i j l) (Wr i l) (W₂ i j l) (Wr j l) (W₃ i j l)).1 t
  have hid₀ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (LinearMap.id : (Q i).T₀ →ₗ[B] (Q i).T₀) := fun i =>
    isLocalizedModule_id (Submonoid.powers (f i)) ((Q i).T₀) (Localization.Away (f i))
  obtain ⟨T₀, _iT₀a, _iT₀m, p₀, hp₀, hp₀c⟩ :=
    IsLocalizedModule.exists_forall_isLocalizedModule_comp_eq_of_span_eq_top f hf (fun i => (Q i).T₀) hid₀
      (fun i j => (Q₂ i j).T₀) ρl₀ ρr₀ hρr₀ hdiag₀ (fun i j l => (Q₃ i j l).T₀) σ₁₀ σ₂₀ σ₃₀ hσ₃₀ hcoc₁₀ hcoc₂₀ hcoc₃₀
  haveI hinv₀ : Module.Invertible B T₀ :=
    Module.Invertible.of_isLocalizedModule_of_span_range_eq_top f hf T₀ (fun i => (Q i).T₀)
      (fun i => Localization.Away (f i)) p₀ hp₀ (fun i => (Q i).invertible₀)

  let ρl₁ : ∀ i j, (Q i).T₁ →ₗ[B] (Q₂ i j).T₁ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wl i j).τ₁
  let ρr₁ : ∀ i j, (Q j).T₁ →ₗ[B] (Q₂ i j).T₁ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wr i j).τ₁
  have hρr₁ : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr₁ i j) := fun i j => by
    haveI : IsLocalization.Away (f j * f i) (C i j) := by rw [mul_comm]; infer_instance
    haveI : IsLocalization.Away (algebraMap B (Localization.Away (f j)) (f i)) (C i j) := away_cancel (f j) (f i)
    exact isLocalizedModule_linB (f i) (Wr i j).τ₁ (Wr i j).span_range_τ₁
  let σ₃₁ : ∀ i j l, (Q₂ j l).T₁ →ₗ[B] (Q₃ i j l).T₁ := fun i j l =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (W₃ i j l).τ₁
  have hσ₃₁ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃₁ i j l) := fun i j l =>
    isLocalizedModule_linB (f i) (W₃ i j l).τ₁ (W₃ i j l).span_range_τ₁
  let σ₁₁ : ∀ i j l, (Q₂ i j).T₁ →ₗ[B] (Q₃ i j l).T₁ := fun i j l => linB (h1 i j l) (hh1 i j l) (W₁ i j l).τ₁
  let σ₂₁ : ∀ i j l, (Q₂ i l).T₁ →ₗ[B] (Q₃ i j l).T₁ := fun i j l => linB (h2 i j l) (hh2 i j l) (W₂ i j l).τ₁
  have hdiag₁ : ∀ i, ρl₁ i i = ρr₁ i i := fun i => by
    apply LinearMap.ext; intro t
    refine (tau_eq_of_eq ?_ (Wl i i) (Wr i i)).2 t
    apply algHom_ext_of_isLocalization (Submonoid.powers (f i))
    · intro b; exact (@IsScalarTower.algebraMap_apply B _ _ _ _ _ _ (_) _ (towBl i i) b).symm
    · intro b; exact (@IsScalarTower.algebraMap_apply B _ _ _ _ _ _ (_) _ (towBr i i) b).symm
  have hcoc₁₁ : ∀ i j l, σ₁₁ i j l ∘ₗ ρl₁ i j = σ₂₁ i j l ∘ₗ ρl₁ i l := fun i j l =>
    LinearMap.ext fun t => (comp_eq_comp _ _ _ _ (hm12 i j l) (Wl i j) (W₁ i j l) (Wl i l) (W₂ i j l)).2 t
  have hcoc₂₁ : ∀ i j l, σ₁₁ i j l ∘ₗ ρr₁ i j = σ₃₁ i j l ∘ₗ ρl₁ j l := fun i j l =>
    LinearMap.ext fun t => (comp_eq_comp _ _ _ _ (hm1 i j l) (Wr i j) (W₁ i j l) (Wl j l) (W₃ i j l)).2 t
  have hcoc₃₁ : ∀ i j l, σ₂₁ i j l ∘ₗ ρr₁ i l = σ₃₁ i j l ∘ₗ ρr₁ j l := fun i j l =>
    LinearMap.ext fun t => (comp_eq_comp _ _ _ _ (hm2 i j l) (Wr i l) (W₂ i j l) (Wr j l) (W₃ i j l)).2 t
  have hid₁ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (LinearMap.id : (Q i).T₁ →ₗ[B] (Q i).T₁) := fun i =>
    isLocalizedModule_id (Submonoid.powers (f i)) ((Q i).T₁) (Localization.Away (f i))
  obtain ⟨T₁, _iT₁a, _iT₁m, p₁, hp₁, hp₁c⟩ :=
    IsLocalizedModule.exists_forall_isLocalizedModule_comp_eq_of_span_eq_top f hf (fun i => (Q i).T₁) hid₁
      (fun i j => (Q₂ i j).T₁) ρl₁ ρr₁ hρr₁ hdiag₁ (fun i j l => (Q₃ i j l).T₁) σ₁₁ σ₂₁ σ₃₁ hσ₃₁ hcoc₁₁ hcoc₂₁ hcoc₃₁
  haveI hinv₁ : Module.Invertible B T₁ :=
    Module.Invertible.of_isLocalizedModule_of_span_range_eq_top f hf T₁ (fun i => (Q i).T₁)
      (fun i => Localization.Away (f i)) p₁ hp₁ (fun i => (Q i).invertible₁)

  obtain ⟨Pi0, Pi1, hA, hB, hC, hD⟩ := piGlue f hf (algebraMap 𝒪 B π)
    (fun i => (Q i).T₀) (fun i => (Q i).T₁) (fun i j => (Q₂ i j).T₀) (fun i j => (Q₂ i j).T₁)
    ρl₀ ρr₀ ρl₁ ρr₁ hρr₀ hρr₁ T₀ T₁ p₀ p₁ hp₀ hp₁ hp₀c hp₁c
    (fun i => ((Q i).Pi₀).restrictScalars B) (fun i => ((Q i).Pi₁).restrictScalars B)
    (fun i m => by
      rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, (Q i).Pi₁_Pi₀,
        IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i)), algebraMap_smul])
    (fun i m => by
      rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, (Q i).Pi₀_Pi₁,
        IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i)), algebraMap_smul])
    (fun i j => ((Q₂ i j).Pi₀).restrictScalars B) (fun i j => ((Q₂ i j).Pi₁).restrictScalars B)
    (fun i j m => (Wl i j).τ₁_Pi₀ m) (fun i j m => (Wr i j).τ₁_Pi₀ m)
    (fun i j m => (Wl i j).τ₀_Pi₁ m) (fun i j m => (Wr i j).τ₀_Pi₁ m)
  refine ⟨T₀, T₁, inferInstance, inferInstance, inferInstance, inferInstance, hinv₀, hinv₁, Pi0, Pi1, p₀, p₁,
    hC, hD, hp₀, hp₁, fun i t => hA i t, fun i t => hB i t, fun i j t => ?_, fun i j t => ?_⟩
  · exact LinearMap.congr_fun (hp₀c i j) t
  · exact LinearMap.congr_fun (hp₁c i j) t

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap (solution)
