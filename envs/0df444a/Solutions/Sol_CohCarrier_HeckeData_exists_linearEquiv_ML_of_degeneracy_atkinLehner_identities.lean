-- Prove2me | solution 1 for CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4f052fde-e5af-55c4-966e-185739fccfb4

import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import Theorems.Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing"
p2m_attr_erase "simp" "IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

noncomputable section

open CohCarrier IsLocalRing

namespace TWAlpha

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

section CompanionOp

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

def comp (T Dinv : Module.End R M) (c : R) : Module.End R (M × M) :=
  (T ∘ₗ LinearMap.fst R M M + c • LinearMap.snd R M M).prod (-(Dinv ∘ₗ LinearMap.fst R M M))

@[scoped simp] private theorem _root_.TWAlpha.comp_apply (T Dinv : Module.End R M) (c : R) (x : M × M) :
    comp T Dinv c x = (T x.1 + c • x.2, -(Dinv x.1)) := rfl

p2m_export "TWAlpha" "comp_apply"

def diag (f : Module.End R M) : Module.End R (M × M) := f.prodMap f

@[scoped simp] theorem diag_apply (f : Module.End R M) (x : M × M) : diag f x = (f x.1, f x.2) := rfl

theorem comp_sq (T Dinv : Module.End R M) (c : R) (h : T * Dinv = Dinv * T) (x : M × M) :
    comp T Dinv c (comp T Dinv c x) = diag T (comp T Dinv c x) - c • diag Dinv x := by
  obtain ⟨x, y⟩ := x
  have h' : T (Dinv x) = Dinv (T x) := congrArg (fun f : Module.End R M => f x) h
  ext <;> simp [map_add, map_smul, map_neg, h'] <;> abel

theorem diag_comp_comm (T Dinv f : Module.End R M) (c : R) (hT : f * T = T * f)
    (hD : f * Dinv = Dinv * f) : diag f * comp T Dinv c = comp T Dinv c * diag f := by
  have hT' : ∀ v, f (T v) = T (f v) := fun v => congrArg (fun g : Module.End R M => g v) hT
  have hD' : ∀ v, f (Dinv v) = Dinv (f v) := fun v => congrArg (fun g : Module.End R M => g v) hD
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> simp [map_add, map_smul, map_neg, hT', hD']

end CompanionOp

section Residue2

variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

def ΘA : Loc D →ₐ[𝒪] k :=
  { Θ D with commutes' := fun a => Θ_algebraMap_base D a }

@[scoped simp] theorem ΘA_apply (z : Loc D) : ΘA D z = Θ D z := rfl

theorem Θ_inverse {z : Loc D} (hz : IsUnit z) : Θ D (Ring.inverse z) = (Θ D z)⁻¹ := by
  have h1 : Θ D z * Θ D (Ring.inverse z) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hz, map_one]
  have hz0 : Θ D z ≠ 0 := (isUnit_iff_Θ_ne_zero D z).mp hz
  field_simp
  rw [mul_comm]; exact h1

theorem algebraMap_smul_ML (f : D.FreeAlg) (x : D.ML) :
    algebraMap D.FreeAlg (Loc D) f • x = f • x :=
  IsScalarTower.algebraMap_smul (Loc D) f x

theorem X_smul_mk (g : D.Gen) (v : V) (s : D.mTheta.primeCompl) :
    (MvPolynomial.X g : D.FreeAlg) • LocalizedModule.mk v s = LocalizedModule.mk (D.op g v) s := by
  rw [LocalizedModule.smul'_mk]
  congr 1
  show D.opAlgHom (MvPolynomial.X g) v = D.op g v
  rw [HeckeData.opAlgHom_X]

theorem X_smul_raw (g : D.Gen) (v : V) : (MvPolynomial.X g : D.FreeAlg) • v = D.op g v := by
  show D.opAlgHom (MvPolynomial.X g) v = D.op g v
  rw [HeckeData.opAlgHom_X]

theorem smul_injective_of_isUnit {z : Loc D} (hz : IsUnit z) {x y : D.ML} (h : z • x = z • y) :
    x = y := by
  have := congrArg (fun w => Ring.inverse z • w) h
  simp only [← mul_smul, Ring.inverse_mul_cancel _ hz, one_smul] at this
  exact this

theorem isUnit_algebraMap_X {g : D.Gen} (hg : D.θbar g ≠ 0) :
    IsUnit (algebraMap D.FreeAlg (Loc D) (MvPolynomial.X g)) :=
  (isUnit_iff_Θ_ne_zero D _).mpr (by rwa [Θ_X])

end Residue2

section CompanionOp2

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

def comp' (T Dinv : Module.End R M) (c : R) : Module.End R (M × M) :=
  ((c • Dinv) ∘ₗ LinearMap.snd R M M).prod (T ∘ₗ LinearMap.snd R M M - LinearMap.fst R M M)

@[scoped simp] theorem comp'_apply (T Dinv : Module.End R M) (c : R) (y : M × M) :
    comp' T Dinv c y = (c • Dinv y.2, T y.2 - y.1) := rfl

theorem comp'_sq (T Dinv : Module.End R M) (c : R) (h : T * Dinv = Dinv * T) (y : M × M) :
    comp' T Dinv c (comp' T Dinv c y) = diag T (comp' T Dinv c y) - c • diag Dinv y := by
  obtain ⟨y₁, y₂⟩ := y
  have h' : ∀ v, T (Dinv v) = Dinv (T v) := fun v => congrArg (fun f : Module.End R M => f v) h
  ext <;> simp [map_sub, map_smul, h', smul_sub]

theorem diag_comp'_comm (T Dinv f : Module.End R M) (c : R) (hT : f * T = T * f)
    (hD : f * Dinv = Dinv * f) : diag f * comp' T Dinv c = comp' T Dinv c * diag f := by
  have hT' : ∀ v, f (T v) = T (f v) := fun v => congrArg (fun g : Module.End R M => g v) hT
  have hD' : ∀ v, f (Dinv v) = Dinv (f v) := fun v => congrArg (fun g : Module.End R M => g v) hD
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> simp [map_sub, map_smul, hT', hD']

end CompanionOp2

section Setting

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V W : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup W] [Module 𝒪 W]
  (DV : HeckeData 𝒪 V k) (DW : HeckeData 𝒪 W k)
  {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σW : G ⊕ Unit ≃ DW.Gen)
  (ι : V →ₗ[𝒪] W) (j : W →ₗ[𝒪] V) (w : Module.End 𝒪 W) (q : ℕ) (d : G)

def DvInv : Module.End 𝒪 V := Ring.inverse (DV.op (σV (Sum.inl d)))

def DwInv : Module.End 𝒪 W := Ring.inverse (DW.op (σW (Sum.inl d)))

section Raw

variable (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
  (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
  (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)
  (hdV : IsUnit (DV.op (σV (Sum.inl d)))) (hdW : IsUnit (DW.op (σW (Sum.inl d))))
  (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
    DV.op (σV (Sum.inl d)))
  (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
  (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
  (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
  (h₅ : w * w = DW.op (σW (Sum.inl d)))

local notation "T♭" => DV.op (σV (Sum.inr ()))
local notation "U♭" => DW.op (σW (Sum.inr ()))
local notation "Dv" => DV.op (σV (Sum.inl d))
local notation "Dw" => DW.op (σW (Sum.inl d))
local notation "Dvi" => DvInv DV σV d
local notation "Dwi" => DwInv DW σW d

include hdV in
theorem Dv_mul_inv : Dv * Dvi = 1 := Ring.mul_inverse_cancel _ hdV
include hdV in
theorem inv_mul_Dv : Dvi * Dv = 1 := Ring.inverse_mul_cancel _ hdV
include hdW in
theorem Dw_mul_inv : Dw * Dwi = 1 := Ring.mul_inverse_cancel _ hdW
include hdW in
theorem inv_mul_Dw : Dwi * Dw = 1 := Ring.inverse_mul_cancel _ hdW

theorem comm_of_comm_inv {R : Type} [Ring R] {f D Di : R} (h : f * D = D * f) (h1 : D * Di = 1)
    (h2 : Di * D = 1) : f * Di = Di * f := by
  calc f * Di = (Di * D) * f * Di := by rw [h2, one_mul]
    _ = Di * (D * f) * Di := by rw [mul_assoc Di D f]
    _ = Di * (f * D) * Di := by rw [h]
    _ = Di * f * (D * Di) := by simp only [mul_assoc]
    _ = Di * f := by rw [h1, mul_one]

include hdV in
theorem T_Dvi_comm : T♭ * Dvi = Dvi * T♭ :=
  comm_of_comm_inv (DV.comm _ _) (Dv_mul_inv DV σV d hdV) (inv_mul_Dv DV σV d hdV)

include hdV in
theorem X_Dvi_comm (g : G) : DV.op (σV (Sum.inl g)) * Dvi = Dvi * DV.op (σV (Sum.inl g)) :=
  comm_of_comm_inv (DV.comm _ _) (Dv_mul_inv DV σV d hdV) (inv_mul_Dv DV σV d hdV)

include hdV h₁ in

theorem U_ι (v : V) : U♭ (ι v) = ι (T♭ v) - w (ι (Dvi v)) := by
  have := congrArg (fun f : V →ₗ[𝒪] W => f (Dvi v)) h₁
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [show Dv (Dvi v) = v from congrArg (fun f : Module.End 𝒪 V => f v) (Dv_mul_inv DV σV d hdV)] at this
  rw [this]; abel

include h₂ h₄ in

theorem U_w_ι (v : V) : U♭ (w (ι v)) = (q : 𝒪) • ι v := by
  have := congrArg (fun f : W →ₗ[𝒪] W => f (ι v)) h₄
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, Module.End.mul_apply] at this
  rw [show j (ι v) = ((q : 𝒪) + 1) • v from congrArg (fun f : V →ₗ[𝒪] V => f v) h₂, map_smul,
    add_smul, one_smul, add_comm ((q : 𝒪) • ι v)] at this
  exact (add_left_cancel this).symm

include h₂ h₄ in

theorem j_U_w (x : W) : j (U♭ (w x)) = (q : 𝒪) • j x := by
  have := congrArg (fun f : W →ₗ[𝒪] W => j (f x)) h₄
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, Module.End.mul_apply,
    map_add] at this
  rw [show j (ι (j x)) = ((q : 𝒪) + 1) • j x from congrArg (fun f : V →ₗ[𝒪] V => f (j x)) h₂,
    add_smul, one_smul, add_comm ((q : 𝒪) • j x)] at this
  exact (add_left_cancel this).symm

include hj hw in

theorem j_w_Dw (x : W) : j (w (Dw x)) = Dv (j (w x)) := by
  rw [show w (Dw x) = Dw (w x) from congrArg (fun f : Module.End 𝒪 W => f x) (hw d),
    show j (Dw (w x)) = Dv (j (w x)) from congrArg (fun f : W →ₗ[𝒪] V => f (w x)) (hj d)]

include h₄ in

theorem U_w_w (z : W) : U♭ (w (w z)) = ι (j (w z)) - w z := by
  have := congrArg (fun f : W →ₗ[𝒪] W => f (w z)) h₄
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, Module.End.mul_apply] at this
  rw [this]; abel

include h₅ in
theorem w_w (z : W) : w (w z) = Dw z := congrArg (fun f : Module.End 𝒪 W => f z) h₅

include hj hw hdV hdW h₂ h₄ h₅ in

theorem j_U (x : W) : j (U♭ x) = (q : 𝒪) • Dvi (j (w x)) := by
  have hx : x = Dw (Dwi x) := (congrArg (fun f : Module.End 𝒪 W => f x) (Dw_mul_inv DW σW d hdW)).symm
  set z := Dwi x
  rw [hx, ← w_w (h₅ := h₅) (z := z), j_U_w (h₂ := h₂) (h₄ := h₄), w_w (h₅ := h₅) (z := z),
    j_w_Dw (hj := hj) (hw := hw),
    show Dvi (Dv (j (w z))) = j (w z) from
      congrArg (fun f : Module.End 𝒪 V => f (j (w z))) (inv_mul_Dv DV σV d hdV)]

include hj hw hdW h₃ h₄ h₅ in

theorem j_w_U (x : W) : j (w (U♭ x)) = T♭ (j (w x)) - j x := by
  have hx : x = Dw (Dwi x) := (congrArg (fun f : Module.End 𝒪 W => f x) (Dw_mul_inv DW σW d hdW)).symm
  set z := Dwi x
  have h3z : j (w (ι (j (w z)))) = T♭ (Dv (j (w z))) := congrArg (fun f : V →ₗ[𝒪] V => f (j (w z))) h₃
  rw [hx, ← w_w (h₅ := h₅) (z := z), U_w_w (h₄ := h₄), map_sub, map_sub, h3z, w_w (h₅ := h₅) (z := z),
    j_w_Dw (hj := hj) (hw := hw)]

include hw h₄ h₅ in

theorem new_relation {x : W} (hx : j x = 0) (hwx : j (w x) = 0) : Dw (U♭ (U♭ x)) = x := by
  have h4x := congrArg (fun f : W →ₗ[𝒪] W => f x) h₄
  have h4wx := congrArg (fun f : W →ₗ[𝒪] W => f (w x)) h₄
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, Module.End.mul_apply, hx, hwx,
    map_zero] at h4x h4wx

  rw [w_w (h₅ := h₅) (z := x)] at h4wx
  have e1 : w x = -(U♭ (Dw x)) := eq_neg_of_add_eq_zero_left h4wx.symm
  have e2 : x = -(U♭ (w x)) := eq_neg_of_add_eq_zero_left h4x.symm
  have hUD : U♭ * Dw = Dw * U♭ := (DW.comm _ _)
  conv_rhs => rw [e2, e1, map_neg, neg_neg]
  show Dw (U♭ (U♭ x)) = U♭ (U♭ (Dw x))
  rw [show U♭ (Dw x) = Dw (U♭ x) from congrArg (fun f : Module.End 𝒪 W => f x) hUD,
    show U♭ (Dw (U♭ x)) = Dw (U♭ (U♭ x)) from congrArg (fun f : Module.End 𝒪 W => f (U♭ x)) hUD]

end Raw

end Setting

section Car

def Car (F V : Type) [Semiring F] [AddCommGroup V] (_m : Module F V) : Type := V

variable {F V : Type} [CommRing F] [AddCommGroup V] (m : Module F V)

scoped instance : AddCommGroup (Car F V m) := inferInstanceAs (AddCommGroup V)
scoped instance instModuleCar : Module F (Car F V m) := m
scoped instance instModuleBaseCar {A : Type} [CommRing A] [Module A V] : Module A (Car F V m) :=
  inferInstanceAs (Module A V)

def toCar {A : Type} [CommRing A] [Module A V] : V →ₗ[A] Car F V m := LinearMap.id

def ofCar {A : Type} [CommRing A] [Module A V] : Car F V m →ₗ[A] V := LinearMap.id

end Car

section Companions

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V W : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup W] [Module 𝒪 W]
  (DV : HeckeData 𝒪 V k) (DW : HeckeData 𝒪 W k)
  {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σW : G ⊕ Unit ≃ DW.Gen)
  (ι : V →ₗ[𝒪] W) (j : W →ₗ[𝒪] V) (w : Module.End 𝒪 W) (q : ℕ) (d : G)
  (hdV : IsUnit (DV.op (σV (Sum.inl d))))

local notation "T♭" => DV.op (σV (Sum.inr ()))
local notation "U♭" => DW.op (σW (Sum.inr ()))
local notation "Dv" => DV.op (σV (Sum.inl d))
local notation "Dw" => DW.op (σW (Sum.inl d))
local notation "Dvi" => DvInv DV σV d
local notation "XV" => fun g : G => DV.op (σV (Sum.inl g))
local notation "YW" => fun g : G => DW.op (σW (Sum.inl g))

def opU : DW.Gen → Module.End 𝒪 (V × V) := fun γ =>
  Sum.elim (fun g => diag (DV.op (σV (Sum.inl g)))) (fun _ => comp T♭ Dvi (q : 𝒪)) (σW.symm γ)

def opU' : DW.Gen → Module.End 𝒪 (V × V) := fun γ =>
  Sum.elim (fun g => diag (DV.op (σV (Sum.inl g)))) (fun _ => comp' T♭ Dvi (q : 𝒪)) (σW.symm γ)

theorem opU_inl (g : G) : opU DV DW σV σW q d (σW (Sum.inl g)) = diag (DV.op (σV (Sum.inl g))) := by
  simp [opU]
theorem opU_inr : opU DV DW σV σW q d (σW (Sum.inr ())) = comp T♭ Dvi (q : 𝒪) := by simp [opU]
theorem opU'_inl (g : G) : opU' DV DW σV σW q d (σW (Sum.inl g)) = diag (DV.op (σV (Sum.inl g))) := by
  simp [opU']
theorem opU'_inr : opU' DV DW σV σW q d (σW (Sum.inr ())) = comp' T♭ Dvi (q : 𝒪) := by simp [opU']

theorem diag_mul_diag (f g : Module.End 𝒪 V) : diag f * diag g = diag (f * g) := by
  apply LinearMap.ext; rintro ⟨x, y⟩; rfl

include hdV in
theorem opU_comm (γ γ' : DW.Gen) :
    opU DV DW σV σW q d γ * opU DV DW σV σW q d γ' = opU DV DW σV σW q d γ' * opU DV DW σV σW q d γ := by
  obtain ⟨x, rfl⟩ := σW.surjective γ
  obtain ⟨x', rfl⟩ := σW.surjective γ'
  rcases x with g | u <;> rcases x' with g' | u'
  · rw [opU_inl, opU_inl, diag_mul_diag, diag_mul_diag, DV.comm]
  · obtain rfl : u' = () := rfl
    rw [opU_inl, opU_inr]
    exact diag_comp_comm _ _ _ _ (DV.comm _ _) (X_Dvi_comm DV σV d hdV g)
  · obtain rfl : u = () := rfl
    rw [opU_inl, opU_inr]
    exact (diag_comp_comm _ _ _ _ (DV.comm _ _) (X_Dvi_comm DV σV d hdV g')).symm
  · obtain rfl : u = () := rfl; obtain rfl : u' = () := rfl; rfl

include hdV in
theorem opU'_comm (γ γ' : DW.Gen) :
    opU' DV DW σV σW q d γ * opU' DV DW σV σW q d γ' = opU' DV DW σV σW q d γ' * opU' DV DW σV σW q d γ := by
  obtain ⟨x, rfl⟩ := σW.surjective γ
  obtain ⟨x', rfl⟩ := σW.surjective γ'
  rcases x with g | u <;> rcases x' with g' | u'
  · rw [opU'_inl, opU'_inl, diag_mul_diag, diag_mul_diag, DV.comm]
  · obtain rfl : u' = () := rfl
    rw [opU'_inl, opU'_inr]
    exact diag_comp'_comm _ _ _ _ (DV.comm _ _) (X_Dvi_comm DV σV d hdV g)
  · obtain rfl : u = () := rfl
    rw [opU'_inl, opU'_inr]
    exact (diag_comp'_comm _ _ _ _ (DV.comm _ _) (X_Dvi_comm DV σV d hdV g')).symm
  · obtain rfl : u = () := rfl; obtain rfl : u' = () := rfl; rfl

abbrev DU : HeckeData 𝒪 (V × V) k :=
  { Gen := DW.Gen, op := opU DV DW σV σW q d, comm := opU_comm DV DW σV σW q d hdV, θbar := DW.θbar }

abbrev DU' : HeckeData 𝒪 (V × V) k :=
  { Gen := DW.Gen, op := opU' DV DW σV σW q d, comm := opU'_comm DV DW σV σW q d hdV, θbar := DW.θbar }

def modP : Module DW.FreeAlg (V × V) := (DU DV DW σV σW q d hdV).moduleFreeAlg

def modP' : Module DW.FreeAlg (V × V) := (DU' DV DW σV σW q d hdV).moduleFreeAlg

local notation "P♯" => Car DW.FreeAlg (V × V) (modP DV DW σV σW q d hdV)
local notation "P'♯" => Car DW.FreeAlg (V × V) (modP' DV DW σV σW q d hdV)

scoped instance instTowerP : IsScalarTower 𝒪 DW.FreeAlg P♯ := (DU DV DW σV σW q d hdV).V_isScalarTower
scoped instance instTowerP' : IsScalarTower 𝒪 DW.FreeAlg P'♯ := (DU' DV DW σV σW q d hdV).V_isScalarTower

theorem X_smul_P (γ : DW.Gen) (x : P♯) :
    (MvPolynomial.X γ : DW.FreeAlg) • x =
      toCar (A := 𝒪) (modP DV DW σV σW q d hdV) (opU DV DW σV σW q d γ (ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) x)) := by
  show (DU DV DW σV σW q d hdV).opAlgHom (MvPolynomial.X γ) x = _
  rw [HeckeData.opAlgHom_X]; rfl

theorem X_smul_P' (γ : DW.Gen) (x : P'♯) :
    (MvPolynomial.X γ : DW.FreeAlg) • x =
      toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) (opU' DV DW σV σW q d γ (ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) x)) := by
  show (DU' DV DW σV σW q d hdV).opAlgHom (MvPolynomial.X γ) x = _
  rw [HeckeData.opAlgHom_X]; rfl

theorem X_smul_W (γ : DW.Gen) (x : W) : (MvPolynomial.X γ : DW.FreeAlg) • x = DW.op γ x := by
  show DW.opAlgHom (MvPolynomial.X γ) x = _
  rw [HeckeData.opAlgHom_X]

@[scoped simp] theorem ofCar_toCar_P (p : V × V) :
    ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) (toCar (A := 𝒪) (modP DV DW σV σW q d hdV) p) = p := rfl
@[scoped simp] theorem ofCar_toCar_P' (p : V × V) :
    ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) (toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) p) = p := rfl

theorem smul_of_X {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module DW.FreeAlg M] [Module DW.FreeAlg N]
    [Module 𝒪 M] [Module 𝒪 N] [IsScalarTower 𝒪 DW.FreeAlg M] [IsScalarTower 𝒪 DW.FreeAlg N]
    (F : M →ₗ[𝒪] N) (hX : ∀ (γ : DW.Gen) (x : M), F ((MvPolynomial.X γ : DW.FreeAlg) • x) =
      (MvPolynomial.X γ : DW.FreeAlg) • F x) (f : DW.FreeAlg) (x : M) : F (f • x) = f • F x := by
  induction f using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [show (MvPolynomial.C a : DW.FreeAlg) = algebraMap 𝒪 DW.FreeAlg a from rfl, algebraMap_smul,
      algebraMap_smul, LinearMap.map_smul]
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
  | mul_X p γ hp => rw [mul_smul, hp, hX, mul_smul]

section Maps

variable (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
  (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
  (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)
  (hdW : IsUnit (DW.op (σW (Sum.inl d))))
  (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
    DV.op (σV (Sum.inl d)))
  (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
  (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
  (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
  (h₅ : w * w = DW.op (σW (Sum.inl d)))

def ιO : (V × V) →ₗ[𝒪] W := ι ∘ₗ LinearMap.fst 𝒪 V V + w ∘ₗ ι ∘ₗ LinearMap.snd 𝒪 V V

theorem ιO_apply (p : V × V) : ιO ι w p = ι p.1 + w (ι p.2) := rfl

include hdV hι hw h₁ h₂ h₄ in
theorem ιO_opU (γ : DW.Gen) (p : V × V) : ιO ι w (opU DV DW σV σW q d γ p) = DW.op γ (ιO ι w p) := by
  obtain ⟨x, rfl⟩ := σW.surjective γ
  obtain ⟨v₁, v₂⟩ := p
  rcases x with g | u
  · rw [opU_inl, ιO_apply, ιO_apply, diag_apply, map_add]
    have h1 : ∀ v, ι (DV.op (σV (Sum.inl g)) v) = DW.op (σW (Sum.inl g)) (ι v) := fun v =>
      congrArg (fun f : V →ₗ[𝒪] W => f v) (hι g)
    have h2 : ∀ y, w (DW.op (σW (Sum.inl g)) y) = DW.op (σW (Sum.inl g)) (w y) := fun y =>
      congrArg (fun f : Module.End 𝒪 W => f y) (hw g)
    simp only [h1, h2]
  · obtain rfl : u = () := rfl
    rw [opU_inr, ιO_apply, ιO_apply, comp_apply, map_add, map_add, map_smul, map_neg, map_neg,
      U_ι (hdV := hdV) (h₁ := h₁), U_w_ι (h₂ := h₂) (h₄ := h₄)]
    abel

def ιF : P♯ →ₗ[DW.FreeAlg] W :=
  { (ιO ι w) ∘ₗ ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) with
    map_smul' := fun f x => by
      refine smul_of_X DW ((ιO ι w) ∘ₗ ofCar (A := 𝒪) (modP DV DW σV σW q d hdV)) (fun γ y => ?_) f x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, X_smul_P, ofCar_toCar_P,
        ιO_opU (hdV := hdV) (hι := hι) (hw := hw) (h₁ := h₁) (h₂ := h₂) (h₄ := h₄), X_smul_W] }

theorem ιF_apply (x : P♯) :
    ιF DV DW σV σW ι j w q d hdV hι hw h₁ h₂ h₄ x = ιO ι w (ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) x) := rfl

def jO : W →ₗ[𝒪] (V × V) := j.prod (j ∘ₗ w)

theorem jO_apply (x : W) : jO j w x = (j x, j (w x)) := rfl

include hj hw hdV hdW h₂ h₃ h₄ h₅ in
theorem jO_opW (γ : DW.Gen) (x : W) : jO j w (DW.op γ x) = opU' DV DW σV σW q d γ (jO j w x) := by
  obtain ⟨y, rfl⟩ := σW.surjective γ
  rcases y with g | u
  · rw [opU'_inl, jO_apply, jO_apply, diag_apply]
    have h1 : ∀ y, j (DW.op (σW (Sum.inl g)) y) = DV.op (σV (Sum.inl g)) (j y) := fun y =>
      congrArg (fun f : W →ₗ[𝒪] V => f y) (hj g)
    have h2 : ∀ y, w (DW.op (σW (Sum.inl g)) y) = DW.op (σW (Sum.inl g)) (w y) := fun y =>
      congrArg (fun f : Module.End 𝒪 W => f y) (hw g)
    simp only [h1, h2]
  · obtain rfl : u = () := rfl
    rw [opU'_inr, jO_apply, jO_apply, comp'_apply, j_U (hj := hj) (hw := hw) (hdV := hdV) (hdW := hdW) (h₂ := h₂) (h₄ := h₄) (h₅ := h₅),
      j_w_U (hj := hj) (hw := hw) (hdW := hdW) (h₃ := h₃) (h₄ := h₄) (h₅ := h₅)]

def jF : W →ₗ[DW.FreeAlg] P'♯ :=
  { toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) ∘ₗ jO j w with
    map_smul' := fun f x => by
      refine smul_of_X DW (toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) ∘ₗ jO j w) (fun γ y => ?_) f x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, X_smul_W,
        jO_opW (hdV := hdV) (hj := hj) (hw := hw) (hdW := hdW) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) (h₅ := h₅),
        X_smul_P', ofCar_toCar_P'] }

theorem jF_apply (x : W) :
    jF DV DW σV σW ι j w q d hdV hj hw hdW h₂ h₃ h₄ h₅ x =
      toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) (jO j w x) := rfl

def adjO : (V × V) →ₗ[𝒪] (V × V) :=
  ((((q : 𝒪) + 1) • Dv) ∘ₗ LinearMap.fst 𝒪 V V - (T♭ * Dv) ∘ₗ LinearMap.snd 𝒪 V V).prod
    (-((T♭ * Dv) ∘ₗ LinearMap.fst 𝒪 V V) + (((q : 𝒪) + 1) • LinearMap.id) ∘ₗ LinearMap.snd 𝒪 V V)

theorem adjO_apply (y : V × V) :
    adjO DV σV q d y = (((q : 𝒪) + 1) • Dv y.1 - T♭ (Dv y.2), -(T♭ (Dv y.1)) + ((q : 𝒪) + 1) • y.2) := rfl

def detV : Module.End 𝒪 V := ((q : 𝒪) + 1) ^ 2 • Dv - T♭ * Dv * T♭ * Dv

theorem detV_apply (v : V) : detV DV σV q d v = ((q : 𝒪) + 1) ^ 2 • Dv v - T♭ (Dv (T♭ (Dv v))) := rfl

theorem T_Dv (v : V) : T♭ (Dv v) = Dv (T♭ v) :=
  congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm (σV (Sum.inr ())) (σV (Sum.inl d)))

include hdV in
theorem Dvi_Dv (v : V) : Dvi (Dv v) = v := congrArg (fun f : Module.End 𝒪 V => f v) (inv_mul_Dv DV σV d hdV)

include hdV in
theorem Dv_Dvi (v : V) : Dv (Dvi v) = v := congrArg (fun f : Module.End 𝒪 V => f v) (Dv_mul_inv DV σV d hdV)

include hdV in

theorem adjO_opU' (γ : DW.Gen) (y : V × V) :
    adjO DV σV q d (opU' DV DW σV σW q d γ y) = opU DV DW σV σW q d γ (adjO DV σV q d y) := by
  obtain ⟨x, rfl⟩ := σW.surjective γ
  obtain ⟨y₁, y₂⟩ := y
  rcases x with g | u
  · rw [opU'_inl, opU_inl, adjO_apply, adjO_apply, diag_apply, diag_apply]
    have hX : ∀ v, DV.op (σV (Sum.inl g)) (Dv v) = Dv (DV.op (σV (Sum.inl g)) v) := fun v =>
      congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm _ _)
    have hXT : ∀ v, DV.op (σV (Sum.inl g)) (T♭ v) = T♭ (DV.op (σV (Sum.inl g)) v) := fun v =>
      congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm _ _)
    simp only [map_sub, map_add, map_neg, LinearMap.map_smul_of_tower, hX, hXT]
  · obtain rfl : u = () := rfl
    rw [opU'_inr, opU_inr, adjO_apply, adjO_apply, comp'_apply, comp_apply]
    simp only [map_sub, map_add, map_neg, LinearMap.map_smul_of_tower, T_Dv DV σV d, Dvi_Dv DV σV d hdV,
      Dv_Dvi DV σV d hdV, Prod.mk.injEq]
    constructor <;> module

def adjF : P'♯ →ₗ[DW.FreeAlg] P♯ :=
  { toCar (A := 𝒪) (modP DV DW σV σW q d hdV) ∘ₗ adjO DV σV q d ∘ₗ ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) with
    map_smul' := fun f x => by
      refine smul_of_X DW (toCar (A := 𝒪) (modP DV DW σV σW q d hdV) ∘ₗ adjO DV σV q d ∘ₗ
        ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV)) (fun γ y => ?_) f x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, X_smul_P',
        ofCar_toCar_P', adjO_opU' DV DW σV σW q d hdV, X_smul_P, ofCar_toCar_P] }

theorem adjF_apply (x : P'♯) : adjF DV DW σV σW q d hdV x =
    toCar (A := 𝒪) (modP DV DW σV σW q d hdV) (adjO DV σV q d (ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) x)) := rfl

def detF : P♯ →ₗ[DW.FreeAlg] P♯ :=
  { toCar (A := 𝒪) (modP DV DW σV σW q d hdV) ∘ₗ diag (detV DV σV q d) ∘ₗ ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) with
    map_smul' := fun f x => by
      refine smul_of_X DW (toCar (A := 𝒪) (modP DV DW σV σW q d hdV) ∘ₗ diag (detV DV σV q d) ∘ₗ
        ofCar (A := 𝒪) (modP DV DW σV σW q d hdV)) (fun γ y => ?_) f x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, X_smul_P,
        ofCar_toCar_P, X_smul_P, ofCar_toCar_P]
      congr 1
      show (diag (detV DV σV q d) * opU DV DW σV σW q d γ) _ = (opU DV DW σV σW q d γ * diag (detV DV σV q d)) _
      congr 1
      have hc : detV DV σV q d * T♭ = T♭ * detV DV σV q d := by
        apply LinearMap.ext; intro v
        simp only [Module.End.mul_apply, detV_apply, map_sub, LinearMap.map_smul_of_tower, T_Dv DV σV d]
      have hd : detV DV σV q d * Dvi = Dvi * detV DV σV q d := by
        apply comm_of_comm_inv _ (Dv_mul_inv DV σV d hdV) (inv_mul_Dv DV σV d hdV)
        apply LinearMap.ext; intro v
        simp only [Module.End.mul_apply, detV_apply, map_sub, LinearMap.map_smul_of_tower, T_Dv DV σV d]
      obtain ⟨z, rfl⟩ := σW.surjective γ
      rcases z with g | u
      · rw [opU_inl, diag_mul_diag, diag_mul_diag]
        congr 1
        apply LinearMap.ext; intro v
        have hX : ∀ v, DV.op (σV (Sum.inl g)) (Dv v) = Dv (DV.op (σV (Sum.inl g)) v) := fun v =>
          congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm _ _)
        have hXT : ∀ v, DV.op (σV (Sum.inl g)) (T♭ v) = T♭ (DV.op (σV (Sum.inl g)) v) := fun v =>
          congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm _ _)
        simp only [Module.End.mul_apply, detV_apply, map_sub, LinearMap.map_smul_of_tower, hX, hXT]
      · obtain rfl : u = () := rfl
        rw [opU_inr]
        exact diag_comp_comm _ _ _ _ hc hd }

theorem detF_apply (x : P♯) : detF DV DW σV σW q d hdV x =
    toCar (A := 𝒪) (modP DV DW σV σW q d hdV) (diag (detV DV σV q d) (ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) x)) := rfl

def detF' : P'♯ →ₗ[DW.FreeAlg] P'♯ :=
  { toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) ∘ₗ diag (detV DV σV q d) ∘ₗ ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) with
    map_smul' := fun f x => by
      refine smul_of_X DW (toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) ∘ₗ diag (detV DV σV q d) ∘ₗ
        ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV)) (fun γ y => ?_) f x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, X_smul_P',
        ofCar_toCar_P', X_smul_P', ofCar_toCar_P']
      congr 1
      show (diag (detV DV σV q d) * opU' DV DW σV σW q d γ) _ = (opU' DV DW σV σW q d γ * diag (detV DV σV q d)) _
      congr 1
      have hc : detV DV σV q d * T♭ = T♭ * detV DV σV q d := by
        apply LinearMap.ext; intro v
        simp only [Module.End.mul_apply, detV_apply, map_sub, LinearMap.map_smul_of_tower, T_Dv DV σV d]
      have hd : detV DV σV q d * Dvi = Dvi * detV DV σV q d := by
        apply comm_of_comm_inv _ (Dv_mul_inv DV σV d hdV) (inv_mul_Dv DV σV d hdV)
        apply LinearMap.ext; intro v
        simp only [Module.End.mul_apply, detV_apply, map_sub, LinearMap.map_smul_of_tower, T_Dv DV σV d]
      obtain ⟨z, rfl⟩ := σW.surjective γ
      rcases z with g | u
      · rw [opU'_inl, diag_mul_diag, diag_mul_diag]
        congr 1
        apply LinearMap.ext; intro v
        have hX : ∀ v, DV.op (σV (Sum.inl g)) (Dv v) = Dv (DV.op (σV (Sum.inl g)) v) := fun v =>
          congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm _ _)
        have hXT : ∀ v, DV.op (σV (Sum.inl g)) (T♭ v) = T♭ (DV.op (σV (Sum.inl g)) v) := fun v =>
          congrArg (fun f : Module.End 𝒪 V => f v) (DV.comm _ _)
        simp only [Module.End.mul_apply, detV_apply, map_sub, LinearMap.map_smul_of_tower, hX, hXT]
      · obtain rfl : u = () := rfl
        rw [opU'_inr]
        exact diag_comp'_comm _ _ _ _ hc hd }

theorem detF'_apply (x : P'♯) : detF' DV DW σV σW q d hdV x =
    toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) (diag (detV DV σV q d) (ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) x)) := rfl

include hj h₂ h₃ h₅ in

theorem jO_ιO (p : V × V) :
    jO j w (ιO ι w p) = (((q : 𝒪) + 1) • p.1 + T♭ (Dv p.2), T♭ (Dv p.1) + ((q : 𝒪) + 1) • Dv p.2) := by
  obtain ⟨v₁, v₂⟩ := p
  have hjι : ∀ v, j (ι v) = ((q : 𝒪) + 1) • v := fun v => congrArg (fun f : V →ₗ[𝒪] V => f v) h₂
  have hjwι : ∀ v, j (w (ι v)) = T♭ (Dv v) := fun v => congrArg (fun f : V →ₗ[𝒪] V => f v) h₃
  have hjD : ∀ y, j (Dw y) = Dv (j y) := fun y => congrArg (fun f : W →ₗ[𝒪] V => f y) (hj d)
  have hww : ∀ y, w (w y) = Dw y := fun y => w_w (h₅ := h₅) (z := y)
  rw [jO_apply, ιO_apply]
  simp only [map_add, hjwι, hww, hjD, hjι, LinearMap.map_smul_of_tower]

include hdV hj h₂ h₃ h₅ in

theorem adjO_jO_ιO (p : V × V) : adjO DV σV q d (jO j w (ιO ι w p)) = diag (detV DV σV q d) p := by
  rw [jO_ιO (hj := hj) (h₂ := h₂) (h₃ := h₃) (h₅ := h₅), adjO_apply, diag_apply, detV_apply, detV_apply]
  obtain ⟨v₁, v₂⟩ := p
  simp only [map_add, LinearMap.map_smul_of_tower, T_Dv DV σV d, Prod.mk.injEq]
  constructor <;> module

include hdV hj h₂ h₃ h₅ in

theorem jO_ιO_adjO (y : V × V) : jO j w (ιO ι w (adjO DV σV q d y)) = diag (detV DV σV q d) y := by
  rw [jO_ιO (hj := hj) (h₂ := h₂) (h₃ := h₃) (h₅ := h₅), adjO_apply, diag_apply, detV_apply, detV_apply]
  obtain ⟨y₁, y₂⟩ := y
  simp only [map_add, map_sub, map_neg, LinearMap.map_smul_of_tower, T_Dv DV σV d, Prod.mk.injEq]
  constructor <;> module

include hw h₄ h₅ in

theorem new_smul {x : W} (hx : jF DV DW σV σW ι j w q d hdV hj hw hdW h₂ h₃ h₄ h₅ x = 0) :
    ((MvPolynomial.X (σW (Sum.inl d)) : DW.FreeAlg) * MvPolynomial.X (σW (Sum.inr ())) *
      MvPolynomial.X (σW (Sum.inr ()))) • x = x := by
  have h : jO j w x = 0 := by
    have := congrArg (ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV)) hx
    rwa [jF_apply, ofCar_toCar_P', map_zero] at this
  rw [jO_apply, Prod.mk_eq_zero] at h
  rw [mul_smul, mul_smul, X_smul_W, X_smul_W, X_smul_W]
  exact new_relation DW σW ι j w d hw h₄ h₅ h.1 h.2

section Local

local notation "S♯" => DW.mTheta.primeCompl
local notation "PL♯" => LocalizedModule DW.mTheta.primeCompl P♯
local notation "PL'♯" => LocalizedModule DW.mTheta.primeCompl P'♯
local notation "ιF♯" => ιF DV DW σV σW ι j w q d hdV hι hw h₁ h₂ h₄
local notation "jF♯" => jF DV DW σV σW ι j w q d hdV hj hw hdW h₂ h₃ h₄ h₅
local notation "adjF♯" => adjF DV DW σV σW q d hdV
local notation "detF♯" => detF DV DW σV σW q d hdV
local notation "detF'♯" => detF' DV DW σV σW q d hdV

def uHat : Loc DW := algebraMap DW.FreeAlg (Loc DW) (MvPolynomial.X (σW (Sum.inr ())))
def dHat : Loc DW := algebraMap DW.FreeAlg (Loc DW) (MvPolynomial.X (σW (Sum.inl d)))
def τP : Loc DW := uHat DW σW + algebraMap 𝒪 (Loc DW) (q : 𝒪) * (Ring.inverse (dHat DW σW d) * Ring.inverse (uHat DW σW))

def δ : Loc DW := dHat DW σW d * ((algebraMap 𝒪 (Loc DW) (q : 𝒪) + 1) ^ 2 - τP DW σW q d * τP DW σW q d * dHat DW σW d)

variable (α β : k) (hα : DW.θbar (σW (Sum.inr ())) = α) (hd : DV.θbar (σV (Sum.inl d)) = 1)
  (hθ : ∀ g : G, DW.θbar (σW (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))
  (hq : ((q : ℕ) : k) = 1) (hαβ : α * β = 1) (hne : α ≠ β)

include hαβ hne in
theorem α_ne_zero : α ≠ 0 := by rintro rfl; rw [zero_mul] at hαβ; exact zero_ne_one hαβ

include hα hαβ hne in
theorem isUnit_uHat : IsUnit (uHat DW σW) := isUnit_algebraMap_X DW (by rw [hα]; exact α_ne_zero α β hαβ hne)

include hd hθ in
theorem isUnit_dHat : IsUnit (dHat DW σW d) := isUnit_algebraMap_X DW (by rw [hθ, hd]; exact one_ne_zero)

theorem Θ_q : Θ DW (algebraMap 𝒪 (Loc DW) (q : 𝒪)) = (q : k) := by rw [Θ_algebraMap_base, map_natCast]

include hα hd hθ hq hαβ hne in
theorem Θ_τP : Θ DW (τP DW σW q d) = α + β := by
  have hα0 := α_ne_zero α β hαβ hne
  rw [τP, map_add, map_mul, map_mul, Θ_inverse DW (isUnit_uHat DW σW α β hα hαβ hne),
    Θ_inverse DW (isUnit_dHat DV DW σV σW d hd hθ), uHat, dHat, Θ_X, Θ_X, hα, hθ, hd, Θ_q, hq]
  rw [show β = α⁻¹ from (eq_inv_of_mul_eq_one_right hαβ)]
  field_simp

include hα hd hθ hq hαβ hne in

theorem isUnit_δ : IsUnit (δ DW σW q d) := by
  rw [isUnit_iff_Θ_ne_zero, δ, map_mul, map_sub, map_pow, map_add, map_one, map_mul, map_mul,
    Θ_τP DV DW σV σW q d α β hα hd hθ hq hαβ hne, dHat, Θ_X, hθ, hd, Θ_q, hq]
  intro h
  apply hne
  have h2 : (α - β) ^ 2 = 0 := by linear_combination (-1 : k) * h - 4 * hαβ
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)

theorem X_smul_mkP (γ : DW.Gen) (x : P♯) (s : S♯) :
    (MvPolynomial.X γ : DW.FreeAlg) • (LocalizedModule.mk x s : PL♯) =
      LocalizedModule.mk (toCar (A := 𝒪) (modP DV DW σV σW q d hdV) (opU DV DW σV σW q d γ (ofCar (A := 𝒪) _ x))) s := by
  rw [LocalizedModule.smul'_mk, X_smul_P]

theorem X_smul_mkP' (γ : DW.Gen) (x : P'♯) (s : S♯) :
    (MvPolynomial.X γ : DW.FreeAlg) • (LocalizedModule.mk x s : PL'♯) =
      LocalizedModule.mk (toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) (opU' DV DW σV σW q d γ (ofCar (A := 𝒪) _ x))) s := by
  rw [LocalizedModule.smul'_mk, X_smul_P']

theorem smul_injective_loc {M : Type} [AddCommGroup M] [Module DW.FreeAlg M] {z : Loc DW} (hz : IsUnit z)
    {x y : LocalizedModule DW.mTheta.primeCompl M} (h : z • x = z • y) : x = y := by
  have := congrArg (fun w => Ring.inverse z • w) h
  simp only [← mul_smul, Ring.inverse_mul_cancel _ hz, one_smul] at this
  exact this

theorem mkP_add (x y : P♯) : (LocalizedModule.mk (x + y) 1 : PL♯) = LocalizedModule.mk x 1 + LocalizedModule.mk y 1 :=
  (LocalizedModule.mkLinearMap DW.mTheta.primeCompl P♯).map_add x y
theorem mkP'_add (x y : P'♯) : (LocalizedModule.mk (x + y) 1 : PL'♯) = LocalizedModule.mk x 1 + LocalizedModule.mk y 1 :=
  (LocalizedModule.mkLinearMap DW.mTheta.primeCompl P'♯).map_add x y
theorem mkP_smul (a : 𝒪) (x : P♯) : (LocalizedModule.mk (a • x) 1 : PL♯) = a • LocalizedModule.mk x 1 := by
  rw [← IsScalarTower.algebraMap_smul DW.FreeAlg a (LocalizedModule.mk x 1), LocalizedModule.smul'_mk, algebraMap_smul]
theorem mkP'_smul (a : 𝒪) (x : P'♯) : (LocalizedModule.mk (a • x) 1 : PL'♯) = a • LocalizedModule.mk x 1 := by
  rw [← IsScalarTower.algebraMap_smul DW.FreeAlg a (LocalizedModule.mk x 1), LocalizedModule.smul'_mk, algebraMap_smul]

include hα hd hθ hαβ hne in

theorem τP_smul_mkP (x : P♯) :
    τP DW σW q d • (LocalizedModule.mk x 1 : PL♯) =
      LocalizedModule.mk (toCar (A := 𝒪) (modP DV DW σV σW q d hdV)
        (diag T♭ (ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) x))) 1 := by
  set p : V × V := ofCar (A := 𝒪) (modP DV DW σV σW q d hdV) x
  change τP DW σW q d • (LocalizedModule.mk (toCar (A := 𝒪) (modP DV DW σV σW q d hdV) p) 1 : PL♯) = _
  have hu := isUnit_uHat DW σW α β hα hαβ hne
  have hdd := isUnit_dHat DV DW σV σW d hd hθ
  apply smul_injective_loc DW (hdd.mul hu)
  have hlhs : dHat DW σW d * uHat DW σW * τP DW σW q d =
      dHat DW σW d * uHat DW σW * uHat DW σW + algebraMap 𝒪 (Loc DW) (q : 𝒪) := by
    rw [τP, mul_add]; congr 1
    calc dHat DW σW d * uHat DW σW * (algebraMap 𝒪 (Loc DW) (q : 𝒪) * (Ring.inverse (dHat DW σW d) *
          Ring.inverse (uHat DW σW)))
        = algebraMap 𝒪 (Loc DW) (q : 𝒪) * ((dHat DW σW d * Ring.inverse (dHat DW σW d)) *
            (uHat DW σW * Ring.inverse (uHat DW σW))) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ hdd, Ring.mul_inverse_cancel _ hu, one_mul, mul_one]
  rw [← mul_smul, hlhs, uHat, dHat]
  simp only [add_smul, mul_smul, algebraMap_smul_loc, X_smul_mkP, ofCar_toCar_P, IsScalarTower.algebraMap_smul,
    mkP_smul', mkP_add', opU_inr, opU_inl]
  congr 1
  show diag Dv (comp T♭ Dvi (q : 𝒪) (comp T♭ Dvi (q : 𝒪) p)) + (q : 𝒪) • p = diag Dv (comp T♭ Dvi (q : 𝒪) (diag T♭ p))
  have hTD : T♭ * Dvi = Dvi * T♭ := T_Dvi_comm DV σV d hdV
  rw [comp_sq _ _ _ hTD p, show diag T♭ (comp T♭ Dvi (q : 𝒪) p) = comp T♭ Dvi (q : 𝒪) (diag T♭ p) from
    congrArg (fun f : Module.End 𝒪 (V × V) => f p) (diag_comp_comm _ _ _ _ rfl hTD), map_sub, map_smul]
  have hDD : ∀ x : V × V, diag Dv (diag Dvi x) = x := fun x => by ext <;> simp [Dv_Dvi DV σV d hdV]
  rw [hDD, sub_add_cancel]
where
  algebraMap_smul_loc (f : DW.FreeAlg) (z : PL♯) : algebraMap DW.FreeAlg (Loc DW) f • z = f • z :=
    IsScalarTower.algebraMap_smul (Loc DW) f z
  mkP_smul' (a : 𝒪) (x : P♯) : a • (LocalizedModule.mk x 1 : PL♯) = LocalizedModule.mk (a • x) 1 :=
    (mkP_smul DV DW σV σW q d hdV a x).symm
  mkP_add' (x y : P♯) : (LocalizedModule.mk x 1 : PL♯) + LocalizedModule.mk y 1 = LocalizedModule.mk (x + y) 1 :=
    (mkP_add DV DW σV σW q d hdV x y).symm

theorem mkP'_smul' (a : 𝒪) (x : P'♯) : a • (LocalizedModule.mk x 1 : PL'♯) = LocalizedModule.mk (a • x) 1 :=
  (mkP'_smul DV DW σV σW q d hdV a x).symm
theorem mkP'_add' (x y : P'♯) :
    (LocalizedModule.mk x 1 : PL'♯) + LocalizedModule.mk y 1 = LocalizedModule.mk (x + y) 1 :=
  (mkP'_add DV DW σV σW q d hdV x y).symm
theorem algebraMap_smul_loc' (f : DW.FreeAlg) (z : PL'♯) : algebraMap DW.FreeAlg (Loc DW) f • z = f • z :=
  IsScalarTower.algebraMap_smul (Loc DW) f z
theorem mkP_sub' (x y : P♯) :
    (LocalizedModule.mk x 1 : PL♯) - LocalizedModule.mk y 1 = LocalizedModule.mk (x - y) 1 :=
  ((LocalizedModule.mkLinearMap DW.mTheta.primeCompl P♯).map_sub x y).symm
theorem mkP'_sub' (x y : P'♯) :
    (LocalizedModule.mk x 1 : PL'♯) - LocalizedModule.mk y 1 = LocalizedModule.mk (x - y) 1 :=
  ((LocalizedModule.mkLinearMap DW.mTheta.primeCompl P'♯).map_sub x y).symm

include hα hd hθ hαβ hne in

theorem τP_smul_mkP' (x : P'♯) :
    τP DW σW q d • (LocalizedModule.mk x 1 : PL'♯) =
      LocalizedModule.mk (toCar (A := 𝒪) (modP' DV DW σV σW q d hdV)
        (diag T♭ (ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) x))) 1 := by
  set p : V × V := ofCar (A := 𝒪) (modP' DV DW σV σW q d hdV) x
  change τP DW σW q d • (LocalizedModule.mk (toCar (A := 𝒪) (modP' DV DW σV σW q d hdV) p) 1 : PL'♯) = _
  have hu := isUnit_uHat DW σW α β hα hαβ hne
  have hdd := isUnit_dHat DV DW σV σW d hd hθ
  apply smul_injective_loc DW (hdd.mul hu)
  have hlhs : dHat DW σW d * uHat DW σW * τP DW σW q d =
      dHat DW σW d * uHat DW σW * uHat DW σW + algebraMap 𝒪 (Loc DW) (q : 𝒪) := by
    rw [τP, mul_add]; congr 1
    calc dHat DW σW d * uHat DW σW * (algebraMap 𝒪 (Loc DW) (q : 𝒪) * (Ring.inverse (dHat DW σW d) *
          Ring.inverse (uHat DW σW)))
        = algebraMap 𝒪 (Loc DW) (q : 𝒪) * ((dHat DW σW d * Ring.inverse (dHat DW σW d)) *
            (uHat DW σW * Ring.inverse (uHat DW σW))) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ hdd, Ring.mul_inverse_cancel _ hu, one_mul, mul_one]
  rw [← mul_smul, hlhs, uHat, dHat]
  simp only [add_smul, mul_smul, algebraMap_smul_loc', X_smul_mkP', ofCar_toCar_P', IsScalarTower.algebraMap_smul,
    mkP'_smul', mkP'_add', opU'_inr, opU'_inl]
  congr 1
  show diag Dv (comp' T♭ Dvi (q : 𝒪) (comp' T♭ Dvi (q : 𝒪) p)) + (q : 𝒪) • p = diag Dv (comp' T♭ Dvi (q : 𝒪) (diag T♭ p))
  have hTD : T♭ * Dvi = Dvi * T♭ := T_Dvi_comm DV σV d hdV
  rw [comp'_sq _ _ _ hTD p, show diag T♭ (comp' T♭ Dvi (q : 𝒪) p) = comp' T♭ Dvi (q : 𝒪) (diag T♭ p) from
    congrArg (fun f : Module.End 𝒪 (V × V) => f p) (diag_comp'_comm _ _ _ _ rfl hTD), map_sub, map_smul]
  have hDD : ∀ x : V × V, diag Dv (diag Dvi x) = x := fun x => by ext <;> simp [Dv_Dvi DV σV d hdV]
  rw [hDD, sub_add_cancel]

theorem algebraMap_q1_sq :
    (algebraMap 𝒪 (Loc DW) (q : 𝒪) + 1) ^ 2 = algebraMap 𝒪 (Loc DW) (((q : 𝒪) + 1) ^ 2) := by
  rw [map_pow, map_add, map_one]

theorem diag_detV_eq (p : V × V) :
    diag Dv ((((q : 𝒪) + 1) ^ 2) • p - diag T♭ (diag T♭ (diag Dv p))) = diag (detV DV σV q d) p := by
  obtain ⟨v₁, v₂⟩ := p
  ext <;> simp only [diag_apply, detV_apply, Prod.smul_mk, Prod.mk_sub_mk, map_sub, LinearMap.map_smul_of_tower,
    T_Dv DV σV d]

include hα hd hθ hαβ hne in

theorem δ_smul_mkP (x : P♯) : δ DW σW q d • (LocalizedModule.mk x 1 : PL♯) = LocalizedModule.mk (detF♯ x) 1 := by
  rw [δ, algebraMap_q1_sq, mul_smul, sub_smul, mul_smul, mul_smul, dHat]
  simp only [τP_smul_mkP.algebraMap_smul_loc, X_smul_mkP, opU_inl, IsScalarTower.algebraMap_smul,
    τP_smul_mkP DV DW σV σW q d hdV α β hα hd hθ hαβ hne, ofCar_toCar_P, τP_smul_mkP.mkP_smul', mkP_sub',
    detF_apply]
  congr 2
  rw [← diag_detV_eq DV σV q d]
  rfl

include hα hd hθ hαβ hne in

theorem δ_smul_mkP' (x : P'♯) : δ DW σW q d • (LocalizedModule.mk x 1 : PL'♯) = LocalizedModule.mk (detF'♯ x) 1 := by
  rw [δ, algebraMap_q1_sq, mul_smul, sub_smul, mul_smul, mul_smul, dHat]
  simp only [algebraMap_smul_loc', X_smul_mkP', opU'_inl, IsScalarTower.algebraMap_smul,
    τP_smul_mkP' DV DW σV σW q d hdV α β hα hd hθ hαβ hne, ofCar_toCar_P', mkP'_smul', mkP'_sub',
    detF'_apply]
  congr 2
  rw [← diag_detV_eq DV σV q d]
  rfl

theorem mk_eq_smul_mk_one {M : Type} [AddCommGroup M] [Module DW.FreeAlg M] (x : M) (s : S♯) :
    (LocalizedModule.mk x s : LocalizedModule DW.mTheta.primeCompl M) =
      Localization.mk 1 s • LocalizedModule.mk x 1 := by
  rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]

include hα hd hθ hαβ hne in
theorem detL_eq (z : PL♯) : LocalizedModule.map DW.mTheta.primeCompl detF♯ z = δ DW σW q d • z := by
  induction z using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk, mk_eq_smul_mk_one DW (detF♯ x), mk_eq_smul_mk_one DW x, ← mul_smul, mul_comm, mul_smul,
      δ_smul_mkP DV DW σV σW q d hdV α β hα hd hθ hαβ hne]

include hα hd hθ hαβ hne in
theorem detL'_eq (z : PL'♯) : LocalizedModule.map DW.mTheta.primeCompl detF'♯ z = δ DW σW q d • z := by
  induction z using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk, mk_eq_smul_mk_one DW (detF'♯ x), mk_eq_smul_mk_one DW x, ← mul_smul, mul_comm, mul_smul,
      δ_smul_mkP' DV DW σV σW q d hdV α β hα hd hθ hαβ hne]

include hdV hj h₂ h₃ h₅ in
theorem adjF_jF_ιF (x : P♯) : adjF♯ (jF♯ (ιF♯ x)) = detF♯ x := by
  rw [adjF_apply, jF_apply, ιF_apply, ofCar_toCar_P', detF_apply,
    adjO_jO_ιO (hdV := hdV) (hj := hj) (h₂ := h₂) (h₃ := h₃) (h₅ := h₅)]

include hdV hj h₂ h₃ h₅ in
theorem jF_ιF_adjF (y : P'♯) : jF♯ (ιF♯ (adjF♯ y)) = detF'♯ y := by
  rw [adjF_apply, jF_apply, ιF_apply, ofCar_toCar_P, detF'_apply,
    jO_ιO_adjO (hdV := hdV) (hj := hj) (h₂ := h₂) (h₃ := h₃) (h₅ := h₅)]

theorem adjL_jL_ιL (z : PL♯) :
    LocalizedModule.map DW.mTheta.primeCompl adjF♯ (LocalizedModule.map DW.mTheta.primeCompl jF♯
      (LocalizedModule.map DW.mTheta.primeCompl ιF♯ z)) = LocalizedModule.map DW.mTheta.primeCompl detF♯ z := by
  induction z using LocalizedModule.induction_on with
  | h x s => simp only [LocalizedModule.map_mk, adjF_jF_ιF DV DW σV σW ι j w q d hdV hι hj hw hdW h₁ h₂ h₃ h₄ h₅]

theorem jL_ιL_adjL (y : PL'♯) :
    LocalizedModule.map DW.mTheta.primeCompl jF♯ (LocalizedModule.map DW.mTheta.primeCompl ιF♯
      (LocalizedModule.map DW.mTheta.primeCompl adjF♯ y)) = LocalizedModule.map DW.mTheta.primeCompl detF'♯ y := by
  induction y using LocalizedModule.induction_on with
  | h x s => simp only [LocalizedModule.map_mk, jF_ιF_adjF DV DW σV σW ι j w q d hdV hι hj hw hdW h₁ h₂ h₃ h₄ h₅]

include hα hd hθ hαβ hne in

theorem jL_injective : Function.Injective (LocalizedModule.map DW.mTheta.primeCompl jF♯) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk, mk_eq_zero_iff] at hz
    obtain ⟨u, hu⟩ := hz
    rw [← LinearMap.map_smul] at hu
    have hnew := new_smul DV DW σV σW ι j w q d hdV hj hw hdW h₂ h₃ h₄ h₅ hu
    set t : DW.FreeAlg := MvPolynomial.X (σW (Sum.inl d)) * MvPolynomial.X (σW (Sum.inr ())) *
      MvPolynomial.X (σW (Sum.inr ())) with ht
    have hmem : t - 1 ∈ DW.mTheta.primeCompl := by
      rw [mem_primeCompl_iff, map_sub, map_one, ht, map_mul, map_mul, HeckeData.thetaTilde, MvPolynomial.aeval_X,
        MvPolynomial.aeval_X, hθ, hd, hα, one_mul, sub_ne_zero]
      intro h2
      apply hne
      calc α = α * (α * β) := by rw [hαβ, mul_one]
        _ = α * α * β := by ring
        _ = β := by rw [h2, one_mul]
    rw [mk_eq_zero_iff]
    refine ⟨⟨t - 1, hmem⟩ * u, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, sub_smul, one_smul, hnew, sub_self]

include hj hdW h₃ h₅ hq hα hd hθ hαβ hne in

theorem ιL_injective : Function.Injective (LocalizedModule.map DW.mTheta.primeCompl ιF♯) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h := adjL_jL_ιL DV DW σV σW ι j w q d hdV hι hj hw hdW h₁ h₂ h₃ h₄ h₅ z
  rw [hz, map_zero, map_zero, detL_eq DV DW σV σW q d hdV α β hα hd hθ hαβ hne] at h
  have := congrArg (fun y => Ring.inverse (δ DW σW q d) • y) h
  simp only [smul_zero, ← mul_smul, Ring.inverse_mul_cancel _ (isUnit_δ DV DW σV σW q d α β hα hd hθ hq hαβ hne),
    one_smul] at this
  exact this.symm

include hj hdW h₃ h₅ hq hα hd hθ hαβ hne in

theorem ιL_surjective : Function.Surjective (LocalizedModule.map DW.mTheta.primeCompl ιF♯) := by
  intro y
  refine ⟨LocalizedModule.map DW.mTheta.primeCompl adjF♯ (LocalizedModule.map DW.mTheta.primeCompl jF♯
    (Ring.inverse (δ DW σW q d) • y)), jL_injective DV DW σV σW ι j w q d hdV hj hw hdW h₂ h₃ h₄ h₅ α β hα hd hθ hαβ hne ?_⟩
  rw [jL_ιL_adjL, detL'_eq DV DW σV σW q d hdV α β hα hd hθ hαβ hne, ← LinearMap.map_smul, ← mul_smul,
    Ring.mul_inverse_cancel _ (isUnit_δ DV DW σV σW q d α β hα hd hθ hq hαβ hne), one_smul]

include hdV ι j w hι hj hw hdW h₁ h₂ h₃ h₄ h₅ hq hα hd hθ hαβ hne in

theorem exists_equiv_WL_PL : ∃ e₁ : DW.ML ≃ₗ[𝒪] PL♯, ∀ (f : DW.FreeAlg) (y : DW.ML), e₁ (f • y) = f • e₁ y := by
  let ιL := LocalizedModule.map DW.mTheta.primeCompl ιF♯
  let E : PL♯ ≃ₗ[Loc DW] DW.ML := LinearEquiv.ofBijective ιL
    ⟨ιL_injective DV DW σV σW ι j w q d hdV hι hj hw hdW h₁ h₂ h₃ h₄ h₅ α β hα hd hθ hq hαβ hne,
     ιL_surjective DV DW σV σW ι j w q d hdV hι hj hw hdW h₁ h₂ h₃ h₄ h₅ α β hα hd hθ hq hαβ hne⟩
  refine ⟨(E.symm).restrictScalars 𝒪, fun f y => ?_⟩
  simp only [LinearEquiv.restrictScalars_apply]
  rw [LinearEquiv.symm_apply_eq, ← IsScalarTower.algebraMap_smul (Loc DW) f (E.symm y), LinearEquiv.map_smul,
    LinearEquiv.apply_symm_apply, IsScalarTower.algebraMap_smul]

end Local

end Maps

section Main

variable [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Module.Finite 𝒪 V]

include hdV in

theorem main (hk : Function.Surjective (algebraMap 𝒪 k))
    (hθ : ∀ g : G, DW.θbar (σW (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))
    (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
    (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
    (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)
    (hdW : IsUnit (DW.op (σW (Sum.inl d))))
    (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
      DV.op (σV (Sum.inl d)))
    (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
    (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
    (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
    (h₅ : w * w = DW.op (σW (Sum.inl d)))
    (hq : (q : k) = 1) (hd : DV.θbar (σV (Sum.inl d)) = 1)
    (α β : k) (hα : DW.θbar (σW (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hαβ : α * β = 1) (hne : α ≠ β) :
    ∃ e : DW.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DW.ML),
      e ((MvPolynomial.X (σW (Sum.inl g)) : DW.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x := by

  obtain ⟨e₁, he₁⟩ := exists_equiv_WL_PL DV DW σV σW ι j w q d hdV hι hj hw hdW h₁ h₂ h₃ h₄ h₅ α β hα hd hθ hq hαβ hne

  have hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k (q : 𝒪) := by
    rw [hαβ, hd, one_mul, map_natCast, hq]
  have hc : algebraMap 𝒪 k (q : 𝒪) ≠ 0 := by rw [map_natCast, hq]; exact one_ne_zero
  obtain ⟨e₂, he₂⟩ := CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion hk DV (DU DV DW σV σW q d hdV)
    σV σW hθ (q : 𝒪) d (DvInv DV σV d) (Dv_mul_inv DV σV d hdV) (inv_mul_Dv DV σV d hdV)
    (fun g => by rw [show (DU DV DW σV σW q d hdV).op = opU DV DW σV σW q d from rfl, opU_inl]; rfl)
    (by rw [show (DU DV DW σV σW q d hdV).op = opU DV DW σV σW q d from rfl, opU_inr]; rfl)
    α β hα hT hprod hc hne

  refine ⟨e₁.trans e₂, fun g x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he₁]
  exact he₂ g (e₁ x)

end Main

end Companions

end TWAlpha
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities.TWAlpha"

open CohCarrier in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))

    {V W : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V] [AddCommGroup W] [Module 𝒪 W]
    (DV : HeckeData 𝒪 V k) (DW : HeckeData 𝒪 W k)

    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σW : G ⊕ Unit ≃ DW.Gen)
    (hθ : ∀ g : G, DW.θbar (σW (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))

    (ι : V →ₗ[𝒪] W) (j : W →ₗ[𝒪] V) (w : Module.End 𝒪 W)
    (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
    (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
    (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)

    (q : ℕ) (d : G) (hdV : IsUnit (DV.op (σV (Sum.inl d)))) (hdW : IsUnit (DW.op (σW (Sum.inl d))))

    (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
      DV.op (σV (Sum.inl d)))
    (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
    (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
    (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
    (h₅ : w * w = DW.op (σW (Sum.inl d)))

    (hq : (q : k) = 1) (hd : DV.θbar (σV (Sum.inl d)) = 1)
    (α β : k) (hα : DW.θbar (σW (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hαβ : α * β = 1) (hne : α ≠ β) :
    ∃ e : DW.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DW.ML),
      e ((MvPolynomial.X (σW (Sum.inl g)) : DW.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x :=
  TWAlpha.main DV DW σV σW ι j w q d hdV hk hθ hι hj hw hdW h₁ h₂ h₃ h₄ h₅ hq hd α β hα hT hαβ hne

end
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities.TWAlpha"

end S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
end P2MW
export P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities (solution)
