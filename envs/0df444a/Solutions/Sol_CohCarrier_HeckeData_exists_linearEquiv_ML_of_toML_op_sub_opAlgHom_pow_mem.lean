-- Prove2me | solution 1 for CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7b3af333-c722-51ca-89d6-23e08d40f1ce

import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing"
p2m_attr_erase "simp" "IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

noncomputable section

open CohCarrier IsLocalRing

namespace TWExt

section Residue

variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

abbrev Loc : Type := Localization D.mTheta.primeCompl

theorem thetaTilde_ne_zero_of_mem (s : D.mTheta.primeCompl) : D.thetaTilde (s : D.FreeAlg) ≠ 0 :=
  fun h => s.2 (by
    show (s : D.FreeAlg) ∈ RingHom.ker D.thetaTilde.toRingHom
    exact h)

theorem mem_primeCompl_iff (f : D.FreeAlg) : f ∈ D.mTheta.primeCompl ↔ D.thetaTilde f ≠ 0 := by
  show f ∉ RingHom.ker D.thetaTilde.toRingHom ↔ _
  rw [RingHom.mem_ker]
  rfl

def Θ : Loc D →+* k :=
  IsLocalization.lift (M := D.mTheta.primeCompl) (g := D.thetaTilde.toRingHom)
    (fun s => isUnit_iff_ne_zero.mpr (thetaTilde_ne_zero_of_mem D s))

@[scoped simp] theorem Θ_algebraMap (f : D.FreeAlg) : Θ D (algebraMap D.FreeAlg (Loc D) f) = D.thetaTilde f :=
  IsLocalization.lift_eq _ f

theorem Θ_algebraMap_base (a : 𝒪) : Θ D (algebraMap 𝒪 (Loc D) a) = algebraMap 𝒪 k a := by
  rw [IsScalarTower.algebraMap_apply 𝒪 D.FreeAlg (Loc D), Θ_algebraMap, AlgHom.commutes]

theorem Θ_X (g : D.Gen) : Θ D (algebraMap D.FreeAlg (Loc D) (MvPolynomial.X g)) = D.θbar g := by
  rw [Θ_algebraMap]
  show MvPolynomial.aeval D.θbar (MvPolynomial.X g) = D.θbar g
  exact MvPolynomial.aeval_X _ g

theorem isUnit_iff_Θ_ne_zero (z : Loc D) : IsUnit z ↔ Θ D z ≠ 0 := by
  constructor
  · intro hz h0
    exact not_isUnit_zero (h0 ▸ hz.map (Θ D))
  · intro hz
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective D.mTheta.primeCompl z
    apply (IsLocalization.AtPrime.isUnit_mk'_iff (Loc D) D.mTheta f s).mpr
    rw [mem_primeCompl_iff]
    intro hf
    apply hz
    show Θ D (IsLocalization.mk' (Loc D) f s) = 0
    rw [Θ, IsLocalization.lift_mk'_spec]
    show D.thetaTilde f = D.thetaTilde s * 0
    rw [hf, mul_zero]

theorem isUnit_algebraMap_of_ne (f : D.FreeAlg) (hf : D.thetaTilde f ≠ 0) :
    IsUnit (algebraMap D.FreeAlg (Loc D) f) :=
  (isUnit_iff_Θ_ne_zero D _).mpr (by rwa [Θ_algebraMap])

theorem mem_maximalIdeal_iff_Θ_eq_zero (z : Loc D) : z ∈ maximalIdeal (Loc D) ↔ Θ D z = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_Θ_ne_zero, not_not]

end Residue

section LocMod

variable {R : Type} [CommRing R] {S : Submonoid R} {M : Type} [AddCommGroup M] [Module R M]

theorem mk_eq_zero_iff (m : M) (s : S) :
    LocalizedModule.mk m s = 0 ↔ ∃ u : S, (u : R) • m = 0 := by
  rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
  simp only [smul_zero, Submonoid.smul_def]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u * s, by rw [Submonoid.coe_mul, mul_smul]; exact hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [smul_comm, hu, smul_zero]⟩

theorem isUnit_smul_loc (s : S) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S M)) s) :=
  IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) s

theorem smul_loc_injective (s : S) {x y : LocalizedModule S M} (h : (s : R) • x = (s : R) • y) :
    x = y :=
  (Module.End.isUnit_iff _).mp (isUnit_smul_loc (M := M) s) |>.1 h

end LocMod

section Car

def Car (F M : Type) [Semiring F] [AddCommGroup M] (_m : Module F M) : Type := M

variable {F M : Type} [CommRing F] [AddCommGroup M] (m : Module F M)

scoped instance : AddCommGroup (Car F M m) := inferInstanceAs (AddCommGroup M)
scoped instance instModuleCar : Module F (Car F M m) := m
scoped instance instModuleBaseCar {A : Type} [CommRing A] [Module A M] : Module A (Car F M m) :=
  inferInstanceAs (Module A M)

def toCar {A : Type} [CommRing A] [Module A M] : M →ₗ[A] Car F M m := LinearMap.id

def ofCar {A : Type} [CommRing A] [Module A M] : Car F M m →ₗ[A] M := LinearMap.id

end Car

section Setting

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V]
  (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
  (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g) (z₀ : DV.FreeAlg)

local notation "FV" => DV.FreeAlg
local notation "FE" => DE.FreeAlg
local notation "SV" => DV.mTheta.primeCompl
local notation "SE" => DE.mTheta.primeCompl

local notation "Z♭" => DE.op (σ (Sum.inr ()))

theorem X_smul_V (g : DV.Gen) (v : V) : (MvPolynomial.X g : FV) • v = DV.op g v := by
  show DV.opAlgHom (MvPolynomial.X g) v = _; rw [HeckeData.opAlgHom_X]

theorem X_smul_E (γ : DE.Gen) (v : V) : (MvPolynomial.X γ : FE) • v = DE.op γ v := by
  show DE.opAlgHom (MvPolynomial.X γ) v = _; rw [HeckeData.opAlgHom_X]

include hop in
theorem Z_comm (g : DV.Gen) : Z♭ * DV.op g = DV.op g * Z♭ := by
  rw [← hop]; exact DE.comm _ _

include hop in
theorem Z_smulF (f : FV) (v : V) : Z♭ (f • v) = f • Z♭ v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [show (MvPolynomial.C a : FV) = algebraMap 𝒪 FV a from rfl, algebraMap_smul, algebraMap_smul,
      LinearMap.map_smul]
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
  | mul_X p g hp =>
    rw [mul_smul, hp, X_smul_V, mul_smul, X_smul_V, ← Module.End.mul_apply, Z_comm DV DE σ hop g,
      Module.End.mul_apply]

def ZF : V →ₗ[FV] V :=
  { Z♭ with map_smul' := fun f v => Z_smulF DV DE σ hop f v }

@[scoped simp] theorem ZF_apply (v : V) : ZF DV DE σ hop v = Z♭ v := rfl

def ZL : DV.ML →ₗ[Loc DV] DV.ML := LocalizedModule.map DV.mTheta.primeCompl (ZF DV DE σ hop)

theorem ZL_mk (v : V) (s : SV) : ZL DV DE σ hop (LocalizedModule.mk v s) = LocalizedModule.mk (Z♭ v) s := by
  rw [ZL, LocalizedModule.map_mk]; rfl

def ρV : FV →ₐ[𝒪] Module.End 𝒪 DV.ML := Algebra.lsmul 𝒪 𝒪 DV.ML

@[scoped simp] theorem ρV_apply (f : FV) (x : DV.ML) : ρV DV f x = f • x := rfl

def opML : DE.Gen → Module.End 𝒪 DV.ML := fun γ =>
  Sum.elim (fun g => ρV DV (MvPolynomial.X g)) (fun _ => (ZL DV DE σ hop).restrictScalars 𝒪) (σ.symm γ)

theorem opML_inl (g : DV.Gen) : opML DV DE σ hop (σ (Sum.inl g)) = ρV DV (MvPolynomial.X g) := by simp [opML]
theorem opML_inr : opML DV DE σ hop (σ (Sum.inr ())) = (ZL DV DE σ hop).restrictScalars 𝒪 := by simp [opML]

theorem ZL_smulF (f : FV) (x : DV.ML) : ZL DV DE σ hop (f • x) = f • ZL DV DE σ hop x := by
  rw [← IsScalarTower.algebraMap_smul (Loc DV) f x, LinearMap.map_smul, IsScalarTower.algebraMap_smul]

theorem opML_comm (γ γ' : DE.Gen) :
    opML DV DE σ hop γ * opML DV DE σ hop γ' = opML DV DE σ hop γ' * opML DV DE σ hop γ := by
  obtain ⟨x, rfl⟩ := σ.surjective γ
  obtain ⟨x', rfl⟩ := σ.surjective γ'
  apply LinearMap.ext; intro y
  rcases x with g | u <;> rcases x' with g' | u'
  · simp only [opML_inl, Module.End.mul_apply, ρV_apply, ← mul_smul, mul_comm]
  · obtain rfl : u' = () := rfl
    simp only [opML_inl, opML_inr, Module.End.mul_apply, ρV_apply, LinearMap.restrictScalars_apply, ZL_smulF]
  · obtain rfl : u = () := rfl
    simp only [opML_inl, opML_inr, Module.End.mul_apply, ρV_apply, LinearMap.restrictScalars_apply, ZL_smulF]
  · rfl

abbrev DML : HeckeData 𝒪 DV.ML k :=
  { Gen := DE.Gen, op := opML DV DE σ hop, comm := opML_comm DV DE σ hop, θbar := DE.θbar }

@[reducible] def modN : Module FE DV.ML := (DML DV DE σ hop).moduleFreeAlg

local notation "N♯" => Car FE DV.ML (modN DV DE σ hop)

scoped instance instTowerN : IsScalarTower 𝒪 FE N♯ := (DML DV DE σ hop).V_isScalarTower

theorem X_smul_N (γ : DE.Gen) (x : N♯) :
    (MvPolynomial.X γ : FE) • x = toCar (A := 𝒪) (modN DV DE σ hop) (opML DV DE σ hop γ (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  show (DML DV DE σ hop).opAlgHom (MvPolynomial.X γ) x = _
  rw [HeckeData.opAlgHom_X]; rfl

theorem X_inl_smul_N (g : DV.Gen) (x : N♯) :
    (MvPolynomial.X (σ (Sum.inl g)) : FE) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) ((MvPolynomial.X g : FV) • ofCar (A := 𝒪) (modN DV DE σ hop) x) := by
  rw [X_smul_N, opML_inl]; rfl

theorem X_inr_smul_N (x : N♯) :
    (MvPolynomial.X (σ (Sum.inr ())) : FE) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) (ZL DV DE σ hop (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  rw [X_smul_N, opML_inr]; rfl

theorem C_smul_N (a : 𝒪) (x : N♯) : (MvPolynomial.C a : FE) • x = a • x := by
  rw [show (MvPolynomial.C a : FE) = algebraMap 𝒪 FE a from rfl, algebraMap_smul]

@[scoped simp] theorem ofCar_toCar_N (y : DV.ML) :
    ofCar (A := 𝒪) (modN DV DE σ hop) (toCar (A := 𝒪) (modN DV DE σ hop) y) = y := rfl
@[scoped simp] theorem toCar_ofCar_N (x : N♯) :
    toCar (A := 𝒪) (modN DV DE σ hop) (ofCar (A := 𝒪) (modN DV DE σ hop) x) = x := rfl
theorem toCar_add (y y' : DV.ML) : toCar (A := 𝒪) (modN DV DE σ hop) (y + y') =
    toCar (A := 𝒪) (modN DV DE σ hop) y + toCar (A := 𝒪) (modN DV DE σ hop) y' := rfl
theorem toCar_smulO (a : 𝒪) (y : DV.ML) : toCar (A := 𝒪) (modN DV DE σ hop) (a • y) =
    a • toCar (A := 𝒪) (modN DV DE σ hop) y := rfl
theorem toCar_injective : Function.Injective (toCar (A := 𝒪) (modN DV DE σ hop)) := fun _ _ h => h

def ren : FV →ₐ[𝒪] FE := MvPolynomial.rename (fun g => σ (Sum.inl g))

def sub : FE →ₐ[𝒪] FV :=
  MvPolynomial.aeval (fun γ => Sum.elim (fun g => MvPolynomial.X g) (fun _ => z₀) (σ.symm γ))

@[scoped simp] theorem ren_X (g : DV.Gen) : ren DV DE σ (MvPolynomial.X g) = MvPolynomial.X (σ (Sum.inl g)) := by
  simp [ren]
@[scoped simp] theorem sub_X_inl (g : DV.Gen) : sub DV DE σ z₀ (MvPolynomial.X (σ (Sum.inl g))) = MvPolynomial.X g := by
  simp [sub]
@[scoped simp] theorem sub_X_inr : sub DV DE σ z₀ (MvPolynomial.X (σ (Sum.inr ()))) = z₀ := by
  simp [sub]

theorem ren_smul_N (p : FV) (x : N♯) :
    ren DV DE σ p • x = toCar (A := 𝒪) (modN DV DE σ hop) (p • ofCar (A := 𝒪) (modN DV DE σ hop) x) := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [ren, MvPolynomial.rename_C, C_smul_N, show (MvPolynomial.C a : FV) = algebraMap 𝒪 FV a from rfl,
      algebraMap_smul]; rfl
  | add p q hp hq => rw [map_add, add_smul, hp, hq, add_smul, toCar_add]
  | mul_X p g hp =>
    rw [map_mul, ren_X, mul_smul, X_inl_smul_N, hp, ofCar_toCar_N, mul_smul]

theorem exists_decomp (f : FE) : ∃ h : FE,
    f = ren DV DE σ (sub DV DE σ z₀ f) + (MvPolynomial.X (σ (Sum.inr ())) - ren DV DE σ z₀) * h := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [ren, sub]⟩
  | add p q hp hq =>
    obtain ⟨h₁, e₁⟩ := hp; obtain ⟨h₂, e₂⟩ := hq
    exact ⟨h₁ + h₂, by rw [map_add, map_add, mul_add]; nth_rw 1 [e₁]; nth_rw 1 [e₂]; ring⟩
  | mul_X p γ hp =>
    obtain ⟨h, e⟩ := hp
    obtain ⟨x, rfl⟩ := σ.surjective γ
    rcases x with g | u
    · refine ⟨h * MvPolynomial.X (σ (Sum.inl g)), ?_⟩
      rw [map_mul, sub_X_inl, map_mul, ren_X]; nth_rw 1 [e]; ring
    · obtain rfl : u = () := rfl
      refine ⟨ren DV DE σ (sub DV DE σ z₀ p) + h * MvPolynomial.X (σ (Sum.inr ())), ?_⟩
      rw [map_mul, sub_X_inr, map_mul]
      nth_rw 1 [e]; ring

def fN : V →ₗ[FE] N♯ :=
  { toCar (A := 𝒪) (modN DV DE σ hop) ∘ₗ DV.toMLₒ with
    map_smul' := fun f v => by
      induction f using MvPolynomial.induction_on generalizing v with
      | C a =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
        rw [show (MvPolynomial.C a : FE) = algebraMap 𝒪 FE a from rfl, algebraMap_smul, algebraMap_smul,
          LinearMap.map_smul]
      | add p q hp hq =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hp hq ⊢
        rw [add_smul, map_add, hp, hq, add_smul]
      | mul_X p γ hp =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hp ⊢
        rw [mul_smul, hp, mul_smul]
        congr 1
        obtain ⟨x, rfl⟩ := σ.surjective γ
        rcases x with g | u
        · rw [X_inl_smul_N, LinearMap.comp_apply, LinearMap.comp_apply, ofCar_toCar_N, X_smul_E, hop,
            HeckeData.toMLₒ_apply, HeckeData.toMLₒ_apply, ← X_smul_V DV g v, LinearMap.map_smul]
        · obtain rfl : u = () := rfl
          rw [X_inr_smul_N, LinearMap.comp_apply, LinearMap.comp_apply, ofCar_toCar_N, X_smul_E,
            HeckeData.toMLₒ_apply, HeckeData.toMLₒ_apply]
          congr 1
          show DV.toML (Z♭ v) = ZL DV DE σ hop (LocalizedModule.mk v 1)
          rw [ZL_mk]; rfl }

theorem fN_apply (v : V) : fN DV DE σ hop v = toCar (A := 𝒪) (modN DV DE σ hop) (DV.toML v) := rfl

def mN : Submodule 𝒪 DV.ML := (maximalIdeal 𝒪) • ⊤

theorem smul_mem_mN_of_mem {a : 𝒪} (ha : a ∈ maximalIdeal 𝒪) (y : DV.ML) : a • y ∈ mN DV :=
  Submodule.smul_mem_smul ha Submodule.mem_top

theorem loc_smul_mem_mN (r : Loc DV) {y : DV.ML} (hy : y ∈ mN DV) : r • y ∈ mN DV := by
  refine Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [smul_comm]; exact smul_mem_mN_of_mem DV ha _
  · rw [smul_add]; exact Submodule.add_mem _ hy hy'

theorem F_smul_mem_mN (f : FV) {y : DV.ML} (hy : y ∈ mN DV) : f • y ∈ mN DV := by
  rw [← IsScalarTower.algebraMap_smul (Loc DV) f y]; exact loc_smul_mem_mN DV _ hy

theorem ZL_mem_mN {y : DV.ML} (hy : y ∈ mN DV) : ZL DV DE σ hop y ∈ mN DV := by
  refine Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [LinearMap.map_smul_of_tower]; exact smul_mem_mN_of_mem DV ha _
  · rw [map_add]; exact Submodule.add_mem _ hy hy'

theorem FE_smul_mem_mN (f : FE) {x : N♯} (hx : ofCar (A := 𝒪) (modN DV DE σ hop) x ∈ mN DV) :
    ofCar (A := 𝒪) (modN DV DE σ hop) (f • x) ∈ mN DV := by
  induction f using MvPolynomial.induction_on generalizing x with
  | C a => rw [C_smul_N]; exact Submodule.smul_mem _ a hx
  | add p q hp hq => rw [add_smul]; exact Submodule.add_mem _ (hp hx) (hq hx)
  | mul_X p γ hp =>
    rw [mul_smul]
    apply hp
    obtain ⟨y, rfl⟩ := σ.surjective γ
    rcases y with g | u
    · rw [X_inl_smul_N, ofCar_toCar_N]; exact F_smul_mem_mN DV _ hx
    · obtain rfl : u = () := rfl
      rw [X_inr_smul_N, ofCar_toCar_N]; exact ZL_mem_mN DV DE σ hop hx

def NL : Module.End 𝒪 DV.ML := (ZL DV DE σ hop).restrictScalars 𝒪 - (ρV DV z₀ : Module.End 𝒪 DV.ML)

theorem NL_apply (y : DV.ML) : NL DV DE σ hop z₀ y = ZL DV DE σ hop y - z₀ • y := rfl

theorem Xz_sub_smul_N (x : N♯) :
    ((MvPolynomial.X (σ (Sum.inr ())) : FE) - ren DV DE σ z₀) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) (NL DV DE σ hop z₀ (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  rw [sub_smul, X_inr_smul_N, ren_smul_N]; rfl

theorem toML_Zsub (v : V) :
    DV.toML ((Z♭ - DV.opAlgHom z₀) v) = (NL DV DE σ hop z₀) (DV.toML v) := by
  rw [LinearMap.sub_apply, NL_apply, map_sub, show DV.opAlgHom z₀ v = z₀ • v from rfl, LinearMap.map_smul]
  congr 1
  show DV.toML (Z♭ v) = ZL DV DE σ hop (LocalizedModule.mk v 1)
  rw [ZL_mk]; rfl

theorem toML_Zsub_pow (n : ℕ) (v : V) :
    DV.toML (((Z♭ - DV.opAlgHom z₀) ^ n) v) =
      (NL DV DE σ hop z₀ ^ n) (DV.toML v) := by
  induction n generalizing v with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, toML_Zsub DV DE σ hop, ← Module.End.mul_apply, ← pow_succ]

theorem Xz_sub_pow_smul_N (n : ℕ) (x : N♯) :
    (((MvPolynomial.X (σ (Sum.inr ())) : FE) - ren DV DE σ z₀) ^ n) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) ((NL DV DE σ hop z₀ ^ n)
        (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  induction n generalizing x with
  | zero => rw [pow_zero, one_smul, pow_zero, Module.End.one_apply]; rfl
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, Xz_sub_smul_N, ofCar_toCar_N, pow_succ', Module.End.mul_apply]

theorem NL_loc_smul (r : Loc DV) (y : DV.ML) :
    (NL DV DE σ hop z₀) (r • y) = r • (NL DV DE σ hop z₀) y := by
  rw [NL_apply, NL_apply, LinearMap.map_smul, smul_sub, ← IsScalarTower.algebraMap_smul (Loc DV) z₀ (r • y),
    ← IsScalarTower.algebraMap_smul (Loc DV) z₀ y, ← mul_smul, mul_comm, mul_smul]

theorem NL_pow_loc_smul (n : ℕ) (r : Loc DV) (y : DV.ML) :
    (NL DV DE σ hop z₀ ^ n) (r • y) =
      r • (NL DV DE σ hop z₀ ^ n) y := by
  induction n generalizing y with
  | zero => rw [pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih => rw [pow_succ, Module.End.mul_apply, NL_loc_smul, ih, ← Module.End.mul_apply, ← pow_succ]

variable (n : ℕ)
  (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
    (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML))

include hnil in

theorem NL_pow_mem (y : DV.ML) : (NL DV DE σ hop z₀ ^ n) y ∈ mN DV := by
  induction y using LocalizedModule.induction_on with
  | h v t =>
    have : (LocalizedModule.mk v t : DV.ML) = Localization.mk 1 t • DV.toML v := by
      show _ = _ • LocalizedModule.mk v 1
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [this, NL_pow_loc_smul]
    exact loc_smul_mem_mN DV _ (by rw [← toML_Zsub_pow]; exact hnil v)

include hnil in
theorem Xz_sub_pow_smul_mem (x : N♯) :
    ofCar (A := 𝒪) (modN DV DE σ hop) ((((MvPolynomial.X (σ (Sum.inr ())) : FE) - ren DV DE σ z₀) ^ n) • x) ∈
      mN DV := by
  rw [Xz_sub_pow_smul_N]; exact NL_pow_mem DV DE σ hop z₀ n hnil _

variable (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)
  (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)

include hθ hz in
theorem thetaTilde_sub (f : FE) : DV.thetaTilde (sub DV DE σ z₀ f) = DE.thetaTilde f := by
  suffices h : DV.thetaTilde.comp (sub DV DE σ z₀) = DE.thetaTilde from congrArg (fun φ => φ f) h
  apply MvPolynomial.algHom_ext
  intro γ
  obtain ⟨x, rfl⟩ := σ.surjective γ
  rcases x with g | u
  · rw [AlgHom.comp_apply, sub_X_inl, HeckeData.thetaTilde, MvPolynomial.aeval_X, HeckeData.thetaTilde,
      MvPolynomial.aeval_X, hθ]
  · obtain rfl : u = () := rfl
    rw [AlgHom.comp_apply, sub_X_inr, ← hz]
    show _ = MvPolynomial.aeval DE.θbar (MvPolynomial.X (σ (Sum.inr ())))
    rw [MvPolynomial.aeval_X]

include hθ hz in
theorem sub_mem (s : SE) : sub DV DE σ z₀ (s : FE) ∈ SV := by
  rw [mem_primeCompl_iff, thetaTilde_sub DV DE σ z₀ hθ hz]; exact thetaTilde_ne_zero_of_mem DE s

theorem smul_surjective_of_mem {p : FV} (hp : p ∈ SV) : Function.Surjective (fun y : DV.ML => p • y) := by
  have hu := isUnit_smul_loc (M := V) (⟨p, hp⟩ : SV)
  rw [Module.End.isUnit_iff] at hu
  exact hu.2

include hθ hz hnil in

theorem exists_sub_smul_mem (s : SE) (x : N♯) :
    ∃ y : N♯, ofCar (A := 𝒪) (modN DV DE σ hop) (x - (s : FE) • y) ∈ mN DV := by
  obtain ⟨h, e⟩ := exists_decomp DV DE σ z₀ (s : FE)
  set a : FE := ren DV DE σ (sub DV DE σ z₀ s) with ha
  set b : FE := -((MvPolynomial.X (σ (Sum.inr ())) - ren DV DE σ z₀) * h) with hb
  have hs : (s : FE) = a - b := by rw [ha, hb, sub_neg_eq_add]; exact e

  have hsurj : Function.Surjective (fun y : N♯ => a ^ n • y) := by
    intro y
    obtain ⟨y', hy'⟩ := smul_surjective_of_mem DV (pow_mem (sub_mem DV DE σ z₀ hθ hz s) n)
      (ofCar (A := 𝒪) (modN DV DE σ hop) y)
    refine ⟨toCar (A := 𝒪) (modN DV DE σ hop) y', ?_⟩
    show a ^ n • _ = y
    rw [ha, ← map_pow, ren_smul_N, ofCar_toCar_N]
    exact congrArg _ hy'
  obtain ⟨x'', hx''⟩ := hsurj x
  set P : FE := ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)
  refine ⟨P • x'', ?_⟩
  have key : (s : FE) * P = a ^ n - b ^ n := by rw [hs, mul_comm]; exact geom_sum₂_mul a b n
  rw [← mul_smul, key]
  have hsub : (a ^ n - b ^ n) • x'' = a ^ n • x'' - b ^ n • x'' := sub_smul _ _ _
  rw [hsub, ← hx'', sub_sub_cancel]
  show ofCar (A := 𝒪) (modN DV DE σ hop) (b ^ n • x'') ∈ mN DV
  rw [hb, neg_pow, mul_pow, mul_smul, mul_comm, mul_smul]
  exact FE_smul_mem_mN DV DE σ hop _ (FE_smul_mem_mN DV DE σ hop _ (Xz_sub_pow_smul_mem DV DE σ hop z₀ n hnil _))

include hθ in
theorem thetaTilde_ren (q : FV) : DE.thetaTilde (ren DV DE σ q) = DV.thetaTilde q := by
  suffices h : DE.thetaTilde.comp (ren DV DE σ) = DV.thetaTilde from congrArg (fun φ => φ q) h
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, ren_X, HeckeData.thetaTilde, MvPolynomial.aeval_X, HeckeData.thetaTilde,
    MvPolynomial.aeval_X, hθ]

include hθ in
theorem ren_mem (t : SV) : ren DV DE σ (t : FV) ∈ SE := by
  rw [mem_primeCompl_iff, thetaTilde_ren DV DE σ hθ]; exact thetaTilde_ne_zero_of_mem DV t

include hop in

theorem ren_smul_V (q : FV) (v : V) : (ren DV DE σ q : FE) • v = q • v := by
  induction q using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [ren, MvPolynomial.rename_C, show (MvPolynomial.C a : FE) = algebraMap 𝒪 FE a from rfl, algebraMap_smul,
      show (MvPolynomial.C a : FV) = algebraMap 𝒪 FV a from rfl, algebraMap_smul]
  | add p q hp hq => rw [map_add, add_smul, hp, hq, add_smul]
  | mul_X p g hp => rw [map_mul, ren_X, mul_smul, X_smul_E, hop, ← X_smul_V DV, hp, mul_smul]

section Units

variable [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Module.Finite 𝒪 V]
  (hk : Function.Surjective (algebraMap 𝒪 k))

include hk hθ hz hnil in

theorem smul_bijective (s : SE) : Function.Bijective (fun x : N♯ => (s : FE) • x) := by
  haveI hfin : Module.Finite 𝒪 N♯ := (CohCarrier.HeckeData.finite_ML_and_free_ML hk DV).1
  let φ : N♯ →ₗ[𝒪] N♯ := (LinearMap.lsmul FE N♯ (s : FE)).restrictScalars 𝒪
  have hφ : ∀ x, φ x = (s : FE) • x := fun _ => rfl

  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top (R := 𝒪) (M := N♯))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro x _
    obtain ⟨y, hy⟩ := exists_sub_smul_mem DV DE σ hop z₀ n hnil hθ hz s x
    rw [show x = φ y + (x - (s : FE) • y) by rw [hφ, add_sub_cancel]]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self φ y) hy
  have hinj : Function.Injective φ := OrzechProperty.injective_of_surjective_endomorphism φ hsurj
  exact ⟨hinj, hsurj⟩

include hk hθ hz hnil in

theorem isLocalizedModule_fN : IsLocalizedModule DE.mTheta.primeCompl (fN DV DE σ hop) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    exact smul_bijective DV DE σ hop z₀ n hnil hθ hz hk s
  surj y := by
    induction' hy : ofCar (A := 𝒪) (modN DV DE σ hop) y using LocalizedModule.induction_on with v t
    refine ⟨(v, ⟨ren DV DE σ (t : FV), ren_mem DV DE σ hθ t⟩), ?_⟩
    show (ren DV DE σ (t : FV) : FE) • y = _
    rw [ren_smul_N, hy, fN_apply, LocalizedModule.smul'_mk]
    congr 1
    show (LocalizedModule.mk ((t : FV) • v) t : DV.ML) = LocalizedModule.mk v 1
    rw [LocalizedModule.mk_eq]; exact ⟨1, by simp [Submonoid.smul_def]⟩
  exists_of_eq {v₁ v₂} h := by
    have h' : (LocalizedModule.mk v₁ 1 : DV.ML) = LocalizedModule.mk v₂ 1 := toCar_injective DV DE σ hop h
    rw [LocalizedModule.mk_eq] at h'
    obtain ⟨u, hu⟩ := h'
    refine ⟨⟨ren DV DE σ (u : FV), ren_mem DV DE σ hθ u⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul] at hu
    show (ren DV DE σ (u : FV) : FE) • v₁ = (ren DV DE σ (u : FV) : FE) • v₂
    rw [ren_smul_V DV DE σ hop, ren_smul_V DV DE σ hop]
    exact hu

end Units

end Setting

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

theorem main (hk : Function.Surjective (algebraMap 𝒪 k))
    (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
    (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g)
    (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)
    (z₀ : DV.FreeAlg) (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)
    (n : ℕ) (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
      (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML)) :
    ∃ e : DE.ML ≃ₗ[𝒪] DV.ML, ∀ (g : DV.Gen) (x : DE.ML),
      e ((MvPolynomial.X (σ (Sum.inl g)) : DE.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • e x := by
  haveI := isLocalizedModule_fN DV DE σ hop z₀ n hnil hθ hz hk
  let iso := IsLocalizedModule.iso DE.mTheta.primeCompl (fN DV DE σ hop)
  let c : Car DE.FreeAlg DV.ML (modN DV DE σ hop) ≃ₗ[𝒪] DV.ML :=
    { ofCar (A := 𝒪) (modN DV DE σ hop) with
      invFun := toCar (A := 𝒪) (modN DV DE σ hop)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨(iso.restrictScalars 𝒪).trans c, fun g x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul, X_inl_smul_N]
  rfl

end Main

end TWExt
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt"

open CohCarrier IsLocalRing in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
    (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g)
    (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)

    (z₀ : DV.FreeAlg) (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)

    (n : ℕ) (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
      (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML)) :
    ∃ e : DE.ML ≃ₗ[𝒪] DV.ML, ∀ (g : DV.Gen) (x : DE.ML),
      e ((MvPolynomial.X (σ (Sum.inl g)) : DE.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • e x :=
  TWExt.main hk DV DE σ hop hθ z₀ hz n hnil

end
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt"

end S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
end P2MW
export P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem (solution)
