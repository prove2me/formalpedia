-- Prove2me | solution 1 for Deformation.exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4768b78f-b866-542b-9562-24316749ea60

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u v w₁ w₂ w₃ w₄ w₅ w'

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_map wittHom map_convMul_of_mem_wittHom wittHomMap coe_wittHomMap TruncWitt.shiftLE TruncWitt.map_shiftLE wittHomShiftLE coe_wittHomShiftLE wittHomMap_shiftLE DieudonneModule DieudonneModule.of_eq_of_iff DieudonneModule.map DieudonneModule.map_of TruncWitt.fontaineKer TruncWitt.shiftLE_mem_fontaineKer TruncWitt.mem_fontaineKer_of_shiftLE_mem TruncWitt.map_mem_fontaineKer fontaineHodge mem_fontaineHodge_iff of_mem_fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span"
namespace FontaineExtStab
namespace Descent
p2m_open "Deformation"

variable {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]

noncomputable def d : B →ₗ[A] B ⊗[A] B :=
  (TensorProduct.mk A B B).flip 1 - TensorProduct.mk A B B 1

theorem d_apply (b : B) : d b = b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b := rfl

theorem d_comp_linearMap : (d : B →ₗ[A] B ⊗[A] B) ∘ₗ Algebra.linearMap A B = 0 := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, Algebra.linearMap_apply, d_apply, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul, LinearMap.zero_apply, sub_self]

noncomputable def s : B ⊗[A] (B ⊗[A] B) →ₗ[A] B ⊗[A] B :=
  (LinearMap.mul' A B).rTensor B ∘ₗ (TensorProduct.assoc A B B B).symm.toLinearMap

noncomputable def r : B ⊗[A] B →ₗ[A] B ⊗[A] A :=
  (TensorProduct.mk A B A).flip 1 ∘ₗ LinearMap.mul' A B

theorem homotopy (w : B ⊗[A] B) :
    s ((d : B →ₗ[A] B ⊗[A] B).lTensor B w) = (Algebra.linearMap A B).lTensor B (r w) - w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_self]
  | tmul x y =>
    simp only [s, r, LinearMap.lTensor_tmul, d_apply, TensorProduct.tmul_sub, map_sub,
      LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, LinearMap.mul'_apply, mul_one, LinearMap.flip_apply,
      TensorProduct.mk_apply, Algebra.linearMap_apply, map_one]
  | add x y hx hy => rw [map_add, map_add, hx, map_add, map_add, hy]; abel

theorem exact_lTensor :
    Function.Exact ((Algebra.linearMap A B).lTensor B) ((d : B →ₗ[A] B ⊗[A] B).lTensor B) := by
  intro w
  constructor
  · intro hw
    have := homotopy w
    rw [hw, map_zero] at this
    exact ⟨r w, (sub_eq_zero.1 this.symm)⟩
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, d_comp_linearMap, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

theorem exists_algebraMap_eq [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) : ∃ a : A, algebraMap A B a = b := by
  have hex : Function.Exact (Algebra.linearMap A B) (d : B →ₗ[A] B ⊗[A] B) :=
    Module.FaithfullyFlat.lTensor_reflects_exact A B (Algebra.linearMap A B)
      (d : B →ₗ[A] B ⊗[A] B) exact_lTensor
  have hb' : (d : B →ₗ[A] B ⊗[A] B) b = 0 := by rw [d_apply, hb, sub_self]
  obtain ⟨a, ha⟩ := (hex b).1 hb'
  exact ⟨a, ha⟩

end Deformation.FontaineExtStab.Descent

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_map wittHom map_convMul_of_mem_wittHom wittHomMap coe_wittHomMap TruncWitt.shiftLE TruncWitt.map_shiftLE wittHomShiftLE coe_wittHomShiftLE wittHomMap_shiftLE DieudonneModule DieudonneModule.of_eq_of_iff DieudonneModule.map DieudonneModule.map_of TruncWitt.fontaineKer TruncWitt.shiftLE_mem_fontaineKer TruncWitt.mem_fontaineKer_of_shiftLE_mem TruncWitt.map_mem_fontaineKer fontaineHodge mem_fontaineHodge_iff of_mem_fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span"
namespace FontaineExtStab
p2m_open "Deformation"

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]

noncomputable abbrev red {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y]
    [Algebra 𝓞 Y] (x : X →ₐ[𝓞] Y) : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.map (AlgHom.id k k) x

theorem red_tmul {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (x : X →ₐ[𝓞] Y) (c : k) (r : X) : red (k := k) x (c ⊗ₜ[𝓞] r) = c ⊗ₜ[𝓞] x r := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem red_comp {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w₂} [CommRing Y] [Algebra 𝓞 Y]
    {Z : Type w₃} [CommRing Z] [Algebra 𝓞 Z] (x : X →ₐ[𝓞] Y) (y : Y →ₐ[𝓞] Z) :
    red (k := k) (y.comp x) = (red (k := k) y).comp (red (k := k) x) := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  simp

theorem includeRight_comp {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y]
    [Algebra 𝓞 Y] (x : X →ₐ[𝓞] Y) :
    (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] k ⊗[𝓞] Y).toRingHom.comp x.toRingHom =
      (red (k := k) x).toRingHom.comp
        (Algebra.TensorProduct.includeRight : X →ₐ[𝓞] k ⊗[𝓞] X).toRingHom := by
  refine RingHom.ext fun r => ?_
  simp [Algebra.TensorProduct.includeRight_apply]

theorem red_bialgHom {X : Type w₁} [CommRing X] [Bialgebra 𝓞 X] {Y : Type w'} [CommRing Y]
    [Bialgebra 𝓞 Y] (q : X →ₐc[𝓞] Y) :
    red (k := k) (q : X →ₐ[𝓞] Y) =
      (Bialgebra.TensorProduct.map (BialgHom.id k k) q : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y) := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul]
  rfl

def Cond (p : ℕ) [Fact p.Prime] {X : Type w₁} [CommRing X] [Bialgebra 𝓞 X]
    {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] (χ : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y) : Prop :=
  ∀ (n : ℕ) (m : Deformation.wittHom k p n (k ⊗[𝓞] X)),
    (m : TruncatedWittVector p n (k ⊗[𝓞] X)) ∈ Deformation.TruncWitt.fontaineKer p n
        (Algebra.TensorProduct.includeRight : X →ₐ[𝓞] k ⊗[𝓞] X).toRingHom →
      Deformation.TruncWitt.map χ.toRingHom (m : TruncatedWittVector p n (k ⊗[𝓞] X)) ∈
        Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] k ⊗[𝓞] Y).toRingHom

theorem cond_comp {𝒮 : Type w₁} [CommRing 𝒮] [Bialgebra 𝓞 𝒮] {ℛ : Type w₂} [CommRing ℛ]
    [Bialgebra 𝓞 ℛ] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (q : 𝒮 →ₐc[𝓞] ℛ) (χ : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y) (hχ : Cond p χ) :
    Cond p (χ.comp (Bialgebra.TensorProduct.map (BialgHom.id k k) q :
      k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ)) := by
  intro n m hm
  set qk : k ⊗[𝓞] 𝒮 →ₐc[k] k ⊗[𝓞] ℛ := Bialgebra.TensorProduct.map (BialgHom.id k k) q with hqk
  have hcomm : (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom.comp
      (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom =
      (qk : k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ).toRingHom.comp
        (Algebra.TensorProduct.includeRight : 𝒮 →ₐ[𝓞] k ⊗[𝓞] 𝒮).toRingHom := by
    refine RingHom.ext fun s => ?_
    simp [hqk, Algebra.TensorProduct.includeRight_apply]
  have hm' : (Deformation.wittHomMap p n qk m : TruncatedWittVector p n (k ⊗[𝓞] ℛ)) ∈
      Deformation.TruncWitt.fontaineKer p n
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom := by
    rw [Deformation.coe_wittHomMap]
    exact Deformation.TruncWitt.map_mem_fontaineKer (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom
      (qk : k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ).toRingHom _ hcomm hm
  have := hχ n _ hm'
  rw [Deformation.coe_wittHomMap, Deformation.TruncWitt.map_map] at this
  exact this

theorem cond_map {X : Type w₁} [CommRing X] [Bialgebra 𝓞 X] {Y : Type w₂} [CommRing Y]
    [Algebra 𝓞 Y] {Y' : Type w'} [CommRing Y'] [Algebra 𝓞 Y'] (ι : Y →ₐ[𝓞] Y')
    (χ : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y) (hχ : Cond p χ) :
    Cond p ((red (k := k) ι).comp χ) := by
  intro n m hm
  have := Deformation.TruncWitt.map_mem_fontaineKer ι.toRingHom (red (k := k) ι).toRingHom
    (Algebra.TensorProduct.includeRight : Y' →ₐ[𝓞] k ⊗[𝓞] Y').toRingHom (includeRight_comp ι)
    (hχ n m hm)
  rw [Deformation.TruncWitt.map_map] at this
  exact this

theorem conv_mul_assoc {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C]
    {A : Type*} [CommSemiring A] [Algebra R A] (a b c : WithConv (C →ₐ[R] A)) :
    a * b * c = a * (b * c) :=
  mul_assoc a b c

theorem conv_one_mul {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C]
    {A : Type*} [CommSemiring A] [Algebra R A] (a : WithConv (C →ₐ[R] A)) : 1 * a = a :=
  one_mul a

section Conv

variable {ℛ : Type w₁} [CommRing ℛ]

theorem red_convMul [Bialgebra 𝓞 ℛ] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (f g : ℛ →ₐ[𝓞] Y) :
    red (k := k) (WithConv.toConv f * WithConv.toConv g).ofConv =
      (WithConv.toConv (red (k := k) f) * WithConv.toConv (red (k := k) g)).ofConv := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  let 𝓡 := Coalgebra.Repr.arbitrary 𝓞 r
  rw [← 𝓡.eq]
  simp only [map_sum, TensorProduct.tmul_sum, Algebra.TensorProduct.lift_tmul,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, red_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem red_convOne [Bialgebra 𝓞 ℛ] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] :
    red (k := k) (1 : WithConv (ℛ →ₐ[𝓞] Y)).ofConv =
      (1 : WithConv (k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y)).ofConv := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

variable [HopfAlgebra 𝓞 ℛ]

noncomputable def antipodeAlgHom : ℛ →ₐ[𝓞] ℛ :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode 𝓞 (A := ℛ)) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom_apply (a : ℛ) :
    antipodeAlgHom (𝓞 := 𝓞) a = HopfAlgebra.antipode 𝓞 a := rfl

noncomputable def invPoint {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] (x : ℛ →ₐ[𝓞] Y) :
    ℛ →ₐ[𝓞] Y :=
  x.comp antipodeAlgHom

theorem invPoint_convMul {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] (x : ℛ →ₐ[𝓞] Y) :
    WithConv.toConv (invPoint x) * WithConv.toConv x = 1 := by
  refine WithConv.ofConv_injective (AlgHom.ext fun a => ?_)
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have key := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := 𝓞) a
  let 𝓡 := Coalgebra.Repr.arbitrary 𝓞 a
  rw [← 𝓡.eq] at key ⊢
  simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply] at key
  simp only [map_sum, Algebra.TensorProduct.lift_tmul]
  have : ∑ i ∈ 𝓡.index, (invPoint x) (𝓡.left i) * x (𝓡.right i) =
      x (∑ i ∈ 𝓡.index, HopfAlgebra.antipode 𝓞 (𝓡.left i) * 𝓡.right i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [this, key, AlgHom.commutes]

theorem convMul_invPoint {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] (x : ℛ →ₐ[𝓞] Y) :
    WithConv.toConv x * WithConv.toConv (invPoint x) = 1 := by
  refine WithConv.ofConv_injective (AlgHom.ext fun a => ?_)
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have key := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := 𝓞) a
  let 𝓡 := Coalgebra.Repr.arbitrary 𝓞 a
  rw [← 𝓡.eq] at key ⊢
  simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply] at key
  simp only [map_sum, Algebra.TensorProduct.lift_tmul]
  have : ∑ i ∈ 𝓡.index, x (𝓡.left i) * (invPoint x) (𝓡.right i) =
      x (∑ i ∈ 𝓡.index, 𝓡.left i * HopfAlgebra.antipode 𝓞 (𝓡.right i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [this, key, AlgHom.commutes]

end Conv

section Core

variable (p)
variable {ℛ : Type w₁} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
variable {ℛ₁ : Type w₂} [CommRing ℛ₁] [Bialgebra 𝓞 ℛ₁]
variable {ℛ₃ : Type w₃} [CommRing ℛ₃] [Bialgebra 𝓞 ℛ₃]

theorem core (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Surjective π) (j : ℛ₃ →ₐc[𝓞] ℛ)
    (hexact : RingHom.ker (π : ℛ →ₐ[𝓞] ℛ₁) =
      Ideal.map (j : ℛ₃ →ₐ[𝓞] ℛ) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 ℛ₃)))
    (hL : ∀ z ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] k ⊗[𝓞] ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge k p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom,
        Deformation.DieudonneModule.map k p
          (Bialgebra.TensorProduct.map (BialgHom.id k k) π) y = z)
    {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (χ : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y) (hχ : Cond p χ)
    (x₃ : ℛ₃ →ₐ[𝓞] Y)
    (hx₃ : red x₃ = χ.comp (Bialgebra.TensorProduct.map (BialgHom.id k k) j :
      k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ))
    {Y' : Type w₄} [CommRing Y'] [Algebra 𝓞 Y'] (hpY' : (p : Y') ∈ nonZeroDivisors Y')
    (ι : Y →ₐ[𝓞] Y') (x' : ℛ →ₐ[𝓞] Y') (hsq : x'.comp (j : ℛ₃ →ₐ[𝓞] ℛ) = ι.comp x₃)
    (hG₁ : ∀ ψ : k ⊗[𝓞] ℛ₁ →ₐ[k] k ⊗[𝓞] Y', Cond p ψ → ∃ d : ℛ₁ →ₐ[𝓞] Y', red d = ψ)
    {Y'' : Type w₅} [CommRing Y''] [Algebra 𝓞 Y''] (p₁ p₂ : Y' →ₐ[𝓞] Y'')
    (hp₁₂ : p₁.comp ι = p₂.comp ι)
    (hG : ∀ y y' : ℛ →ₐ[𝓞] Y'', red (k := k) y = red y' → y = y')
    (heq : ∀ y' : Y', p₁ y' = p₂ y' → ∃ y : Y, ι y = y')
    (hι : Injective ι) (hιk : Injective (red (k := k) ι)) :
    ∃ x : ℛ →ₐ[𝓞] Y, red x = χ := by
  classical
  set jk : k ⊗[𝓞] ℛ₃ →ₐc[k] k ⊗[𝓞] ℛ := Bialgebra.TensorProduct.map (BialgHom.id k k) j
    with hjk
  set πk : k ⊗[𝓞] ℛ →ₐc[k] k ⊗[𝓞] ℛ₁ := Bialgebra.TensorProduct.map (BialgHom.id k k) π
    with hπk_def

  set χ' : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y' := (red (k := k) ι).comp χ with hχ'_def
  have hχ' : Cond p χ' := cond_map ι χ hχ

  set xk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y' := red (k := k) x' with hxk_def
  set ik : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y' := red (k := k) (invPoint x') with hik_def
  have hik_xk : WithConv.toConv ik * WithConv.toConv xk = 1 := by
    apply WithConv.ofConv_injective
    rw [hik_def, hxk_def, ← red_convMul, invPoint_convMul, red_convOne]
  have hxk_ik : WithConv.toConv xk * WithConv.toConv ik = 1 := by
    apply WithConv.ofConv_injective
    rw [hik_def, hxk_def, ← red_convMul, convMul_invPoint, red_convOne]

  set δ : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y' := (WithConv.toConv ik * WithConv.toConv χ').ofConv
    with hδ_def

  have hχ'j : χ'.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ) =
      xk.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ) := by
    calc χ'.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ)
        = (red (k := k) ι).comp (χ.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ)) := by
          rw [hχ'_def, AlgHom.comp_assoc]
      _ = (red (k := k) ι).comp (red x₃) := by rw [hx₃]
      _ = red (ι.comp x₃) := (red_comp _ _).symm
      _ = red (x'.comp (j : ℛ₃ →ₐ[𝓞] ℛ)) := by rw [hsq]
      _ = xk.comp (red (k := k) (j : ℛ₃ →ₐ[𝓞] ℛ)) := red_comp _ _
      _ = xk.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ) := by rw [red_bialgHom]

  have hone : ((1 : WithConv (k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y')).ofConv).comp
      (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ) =
      (1 : WithConv (k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] Y')).ofConv := by
    refine AlgHom.ext fun z => ?_
    rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
    exact congrArg (algebraMap k (k ⊗[𝓞] Y')) (CoalgHomClass.counit_comp_apply jk z)
  have hδj : δ.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ) =
      (1 : WithConv (k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] Y')).ofConv := by
    have h1 := hone
    rw [← hik_xk, AlgHom.convMul_comp_bialgHom_distrib] at h1
    rw [hδ_def, AlgHom.convMul_comp_bialgHom_distrib]
    change (WithConv.toConv (ik.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ)) *
      WithConv.toConv (χ'.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ))).ofConv = _
    rw [hχ'j]
    exact h1

  have hπk_apply : ∀ z, (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁) z =
      Algebra.TensorProduct.map (AlgHom.id 𝓞 k) (π : ℛ →ₐ[𝓞] ℛ₁) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c r => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hkerπk : RingHom.ker (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom =
      (RingHom.ker (π : ℛ →ₐ[𝓞] ℛ₁)).map
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ) := by
    rw [← Algebra.TensorProduct.lTensor_ker (A := k) (π : ℛ →ₐ[𝓞] ℛ₁) hπ]
    ext z
    simp only [RingHom.mem_ker]
    exact (hπk_apply z) ▸ Iff.rfl
  have hle : RingHom.ker (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom ≤ RingHom.ker δ.toRingHom := by
    rw [hkerπk, hexact, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker]
    have hs' : Coalgebra.counit (R := 𝓞) s = 0 := hs
    have h1 : (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ) ((j : ℛ₃ →ₐ[𝓞] ℛ) s) =
        jk ((1 : k) ⊗ₜ[𝓞] s) := rfl
    change δ ((Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ) ((j : ℛ₃ →ₐ[𝓞] ℛ) s)) = 0
    rw [h1, show δ (jk ((1 : k) ⊗ₜ[𝓞] s)) = (δ.comp (jk : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] ℛ))
      ((1 : k) ⊗ₜ[𝓞] s) from rfl, hδj, AlgHom.convOne_apply, TensorProduct.counit_tmul, hs',
      zero_smul, map_zero]
  have hπks : Surjective (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom := by
    change Surjective (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁)
    rw [hπk_def, Bialgebra.TensorProduct.map_toAlgHom]
    exact Algebra.TensorProduct.map_surjective _ _ surjective_id hπ
  let δ₀ : k ⊗[𝓞] ℛ₁ →+* k ⊗[𝓞] Y' :=
    (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom.liftOfSurjective hπks ⟨δ.toRingHom, hle⟩
  have hδ₀ : ∀ z, δ₀ (πk z) = δ z := fun z =>
    (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom.liftOfRightInverse_comp_apply _ _
      ⟨δ.toRingHom, hle⟩ z
  let δ₁ : k ⊗[𝓞] ℛ₁ →ₐ[k] k ⊗[𝓞] Y' :=
    { δ₀ with
      commutes' := fun c => by
        have : algebraMap k (k ⊗[𝓞] ℛ₁) c = πk (algebraMap k (k ⊗[𝓞] ℛ) c) :=
          ((πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).commutes c).symm
        change δ₀ (algebraMap k (k ⊗[𝓞] ℛ₁) c) = _
        rw [this, hδ₀, AlgHom.commutes] }
  have hδ₁ : δ₁.comp (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁) = δ := AlgHom.ext hδ₀

  have hcondδ₁ : Cond p δ₁ := by
    intro n m₁ hm₁
    obtain ⟨y, hy, hyz⟩ := hL _ (Deformation.of_mem_fontaineHodge (R := k) hm₁)
    obtain ⟨n', m, hm, rfl⟩ := (Deformation.mem_fontaineHodge_iff y).1 hy
    rw [Deformation.DieudonneModule.map_of, Deformation.DieudonneModule.of_eq_of_iff,
      ← Deformation.wittHomMap_shiftLE] at hyz
    set M := Deformation.wittHomShiftLE k p (k ⊗[𝓞] ℛ) (le_max_left n' n) m with hM
    have hMker : (M : TruncatedWittVector p (max n' n) (k ⊗[𝓞] ℛ)) ∈
        Deformation.TruncWitt.fontaineKer p (max n' n)
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom :=
      Deformation.TruncWitt.shiftLE_mem_fontaineKer _ hm
    have hπY : RingHom.ker (Algebra.TensorProduct.includeRight : Y' →ₐ[𝓞] k ⊗[𝓞] Y').toRingHom ≤
        Ideal.span {(p : Y')} :=
      (Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y') hk hker).le
    have hsY : Surjective (Algebra.TensorProduct.includeRight : Y' →ₐ[𝓞] k ⊗[𝓞] Y').toRingHom :=
      Deformation.SpecialFibre.reduction_surjective hk
    refine Deformation.TruncWitt.mem_fontaineKer_of_shiftLE_mem hpY' hπY hsY (le_max_right n' n) ?_
    rw [← Deformation.TruncWitt.map_shiftLE]
    have hcoe : Deformation.TruncWitt.shiftLE (le_max_right n' n)
        (m₁ : TruncatedWittVector p n (k ⊗[𝓞] ℛ₁)) =
        Deformation.TruncWitt.map (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom
          (M : TruncatedWittVector p (max n' n) (k ⊗[𝓞] ℛ)) := by
      have := congrArg Subtype.val hyz
      rw [Deformation.coe_wittHomMap, Deformation.coe_wittHomShiftLE] at this
      exact this.symm
    rw [hcoe, Deformation.TruncWitt.map_map]
    have hcomp : δ₁.toRingHom.comp (πk : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom = δ.toRingHom :=
      congrArg AlgHom.toRingHom hδ₁
    rw [hcomp]
    have hsum : Deformation.TruncWitt.map δ.toRingHom
        (M : TruncatedWittVector p (max n' n) (k ⊗[𝓞] ℛ)) =
        Deformation.TruncWitt.map ik.toRingHom (M : TruncatedWittVector p (max n' n) (k ⊗[𝓞] ℛ)) +
        Deformation.TruncWitt.map χ'.toRingHom (M : TruncatedWittVector p (max n' n) (k ⊗[𝓞] ℛ)) :=
      Deformation.map_convMul_of_mem_wittHom M.2 (WithConv.toConv ik) (WithConv.toConv χ')
    rw [hsum]
    refine add_mem ?_ (hχ' _ M hMker)
    exact Deformation.TruncWitt.map_mem_fontaineKer (invPoint x').toRingHom ik.toRingHom _
      (includeRight_comp _) hMker
  obtain ⟨d, hd⟩ := hG₁ δ₁ hcondδ₁

  set x'' : ℛ →ₐ[𝓞] Y' :=
    (WithConv.toConv x' * WithConv.toConv (d.comp (π : ℛ →ₐ[𝓞] ℛ₁))).ofConv with hx''
  have hredx'' : red (k := k) x'' = χ' := by
    have h3 : WithConv.toConv xk * (WithConv.toConv ik * WithConv.toConv χ') =
        WithConv.toConv χ' := by
      rw [← conv_mul_assoc, hxk_ik, conv_one_mul]
    rw [hx'', red_convMul, red_comp, red_bialgHom, hd, hδ₁]
    exact congrArg WithConv.ofConv h3

  have hpx : p₁.comp x'' = p₂.comp x'' := by
    apply hG
    rw [red_comp, red_comp, hredx'', hχ'_def, ← AlgHom.comp_assoc, ← red_comp, hp₁₂, red_comp,
      AlgHom.comp_assoc]
  have hxr : ∀ r, ∃ y, ι y = x'' r := fun r => heq _ (AlgHom.congr_fun hpx r)
  choose f hf using hxr
  let x : ℛ →ₐ[𝓞] Y :=
    { toFun := f
      map_one' := hι (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hι (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hι (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hι (by rw [hf, map_add, map_add, hf, hf])
      commutes' := fun o => hι (by rw [hf, AlgHom.commutes, AlgHom.commutes]) }
  have hιx : ι.comp x = x'' := AlgHom.ext hf
  refine ⟨x, ?_⟩
  have key : (red (k := k) ι).comp (red (k := k) x) = (red (k := k) ι).comp χ := by
    rw [← red_comp, hιx, hredx'']
  exact AlgHom.ext fun z => hιk (AlgHom.congr_fun key z)

end Core

section Instantiate

omit [Fact p.Prime] in

theorem natCast_mem_nonZeroDivisors_of_flat (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (Y : Type w')
    [CommRing Y] [Algebra 𝓞 Y] [Module.Flat 𝓞 Y] : (p : Y) ∈ nonZeroDivisors Y := by
  have hreg : IsSMulRegular Y (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun y hy => hreg ?_
  change (p : 𝓞) • y = (p : 𝓞) • (0 : Y)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hy]

variable (p)
variable {ℛ : Type w₁} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
variable {ℛ₁ : Type w₂} [CommRing ℛ₁] [Bialgebra 𝓞 ℛ₁]
variable {ℛ₃ : Type w₃} [CommRing ℛ₃] [Bialgebra 𝓞 ℛ₃]

theorem exists_algHom_red_eq (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Surjective π) (j : ℛ₃ →ₐc[𝓞] ℛ)
    (hexact : RingHom.ker (π : ℛ →ₐ[𝓞] ℛ₁) =
      Ideal.map (j : ℛ₃ →ₐ[𝓞] ℛ) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 ℛ₃)))
    (hff : (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.FaithfullyFlat)
    (hfin : (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.Finite)
    (hL : ∀ z ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] k ⊗[𝓞] ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge k p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom,
        Deformation.DieudonneModule.map k p
          (Bialgebra.TensorProduct.map (BialgHom.id k k) π) y = z)
    (hG₁ : ∀ (Y' : Type (max w₁ w')) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
        [Module.Flat 𝓞 Y'] (ψ : k ⊗[𝓞] ℛ₁ →ₐ[k] k ⊗[𝓞] Y'),
      Cond p ψ → ∃ d : ℛ₁ →ₐ[𝓞] Y', red d = ψ)
    (hG : ∀ (Y' : Type (max w₁ w')) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
        [Module.Flat 𝓞 Y'] (y y' : ℛ →ₐ[𝓞] Y'), red (k := k) y = red y' → y = y')
    {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Flat 𝓞 Y]
    (hG₃ : ∀ ψ : k ⊗[𝓞] ℛ₃ →ₐ[k] k ⊗[𝓞] Y, Cond p ψ → ∃ x : ℛ₃ →ₐ[𝓞] Y, red x = ψ)
    (χ : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y) (hχ : Cond p χ) :
    ∃ x : ℛ →ₐ[𝓞] Y, red x = χ := by
  classical

  obtain ⟨x₃, hx₃⟩ := hG₃ _ (cond_comp j χ hχ)

  letI algR : Algebra ℛ₃ ℛ := (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.toAlgebra
  haveI stR : IsScalarTower 𝓞 ℛ₃ ℛ :=
    IsScalarTower.of_algebraMap_eq fun o => ((j : ℛ₃ →ₐ[𝓞] ℛ).commutes o).symm
  letI algY : Algebra ℛ₃ Y := x₃.toRingHom.toAlgebra
  haveI stY : IsScalarTower 𝓞 ℛ₃ Y := IsScalarTower.of_algebraMap_eq fun o => (x₃.commutes o).symm
  haveI ffR : Module.FaithfullyFlat ℛ₃ ℛ := (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  haveI finR : Module.Finite ℛ₃ ℛ := hfin
  haveI : Module.Flat 𝓞 (Y ⊗[ℛ₃] ℛ) := Module.Flat.trans 𝓞 Y (Y ⊗[ℛ₃] ℛ)
  haveI : Module.Finite 𝓞 (Y ⊗[ℛ₃] ℛ) := Module.Finite.trans Y (Y ⊗[ℛ₃] ℛ)
  have hpY' : (p : Y ⊗[ℛ₃] ℛ) ∈ nonZeroDivisors (Y ⊗[ℛ₃] ℛ) :=
    natCast_mem_nonZeroDivisors_of_flat hp _
  let ι : Y →ₐ[𝓞] Y ⊗[ℛ₃] ℛ := Algebra.TensorProduct.includeLeft
  let x' : ℛ →ₐ[𝓞] Y ⊗[ℛ₃] ℛ :=
    (Algebra.TensorProduct.includeRight : ℛ →ₐ[ℛ₃] Y ⊗[ℛ₃] ℛ).restrictScalars 𝓞
  have hι_eq : ∀ y : Y, ι y = algebraMap Y (Y ⊗[ℛ₃] ℛ) y := fun y => rfl
  have hsq : x'.comp (j : ℛ₃ →ₐ[𝓞] ℛ) = ι.comp x₃ := by
    refine AlgHom.ext fun s => ?_
    change (1 : Y) ⊗ₜ[ℛ₃] (algebraMap ℛ₃ ℛ s) = (algebraMap ℛ₃ Y s) ⊗ₜ[ℛ₃] (1 : ℛ)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

  haveI : Module.Flat 𝓞 ((Y ⊗[ℛ₃] ℛ) ⊗[Y] (Y ⊗[ℛ₃] ℛ)) :=
    Module.Flat.trans 𝓞 (Y ⊗[ℛ₃] ℛ) _
  haveI : Module.Finite 𝓞 ((Y ⊗[ℛ₃] ℛ) ⊗[Y] (Y ⊗[ℛ₃] ℛ)) :=
    Module.Finite.trans (Y ⊗[ℛ₃] ℛ) _
  let p₁ : Y ⊗[ℛ₃] ℛ →ₐ[𝓞] (Y ⊗[ℛ₃] ℛ) ⊗[Y] (Y ⊗[ℛ₃] ℛ) := Algebra.TensorProduct.includeLeft
  let p₂ : Y ⊗[ℛ₃] ℛ →ₐ[𝓞] (Y ⊗[ℛ₃] ℛ) ⊗[Y] (Y ⊗[ℛ₃] ℛ) :=
    (Algebra.TensorProduct.includeRight :
      Y ⊗[ℛ₃] ℛ →ₐ[Y] (Y ⊗[ℛ₃] ℛ) ⊗[Y] (Y ⊗[ℛ₃] ℛ)).restrictScalars 𝓞
  have hp₁₂ : p₁.comp ι = p₂.comp ι := by
    refine AlgHom.ext fun y => ?_
    change (algebraMap Y (Y ⊗[ℛ₃] ℛ) y) ⊗ₜ[Y] (1 : Y ⊗[ℛ₃] ℛ) =
      (1 : Y ⊗[ℛ₃] ℛ) ⊗ₜ[Y] (algebraMap Y (Y ⊗[ℛ₃] ℛ) y)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have heq : ∀ y' : Y ⊗[ℛ₃] ℛ, p₁ y' = p₂ y' → ∃ y : Y, ι y = y' := fun y' h =>
    Descent.exists_algebraMap_eq h
  have hι : Injective ι := FaithfulSMul.algebraMap_injective Y (Y ⊗[ℛ₃] ℛ)
  have hιk : Injective (red (k := k) ι) := by
    have hfac : ∀ z : k ⊗[𝓞] Y, red (k := k) ι z =
        TensorProduct.comm 𝓞 (Y ⊗[ℛ₃] ℛ) k
          (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝓞 Y Y (Y ⊗[ℛ₃] ℛ) k
            (TensorProduct.mk Y (Y ⊗[ℛ₃] ℛ) (Y ⊗[𝓞] k) 1 (TensorProduct.comm 𝓞 k Y z))) := by
      intro z
      set e₁ := TensorProduct.comm 𝓞 (Y ⊗[ℛ₃] ℛ) k
      set e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange 𝓞 Y Y (Y ⊗[ℛ₃] ℛ) k
      set f₃ := TensorProduct.mk Y (Y ⊗[ℛ₃] ℛ) (Y ⊗[𝓞] k) 1
      set e₄ := TensorProduct.comm 𝓞 k Y
      induction z using TensorProduct.induction_on with
      | zero =>
        rw [map_zero (red (k := k) ι), e₄.map_zero, f₃.map_zero, e₂.map_zero, e₁.map_zero]
      | tmul c y =>
        rw [red_tmul, TensorProduct.comm_tmul, TensorProduct.mk_apply,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.comm_tmul,
          hι_eq, Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        rw [map_add (red (k := k) ι), e₄.map_add, f₃.map_add, e₂.map_add, e₁.map_add, hx, hy]
    intro z z' hzz'
    rw [hfac, hfac] at hzz'
    exact (TensorProduct.comm 𝓞 k Y).injective
      (Module.FaithfullyFlat.tensorProduct_mk_injective (A := Y) (B := Y ⊗[ℛ₃] ℛ) (Y ⊗[𝓞] k)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange 𝓞 Y Y (Y ⊗[ℛ₃] ℛ) k).injective
          ((TensorProduct.comm 𝓞 (Y ⊗[ℛ₃] ℛ) k).injective hzz')))

  exact core p hk hker π hπ j hexact hL χ hχ x₃ hx₃ hpY' ι x' hsq
    (fun ψ hψ => hG₁ (Y ⊗[ℛ₃] ℛ) ψ hψ) p₁ p₂ hp₁₂
    (fun y y' h => hG ((Y ⊗[ℛ₃] ℛ) ⊗[Y] (Y ⊗[ℛ₃] ℛ)) y y' h) heq hι hιk

end Instantiate

end Deformation.FontaineExtStab
p2m_reactivate "P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit.Deformation P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit.Deformation.FontaineExtStab"
p2m_reactivate "P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit.Deformation"

open Deformation.FontaineExtStab in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {ℛ : Type w₁} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
    {ℛ₁ : Type w₂} [CommRing ℛ₁] [Bialgebra 𝓞 ℛ₁]
    {ℛ₃ : Type w₃} [CommRing ℛ₃] [Bialgebra 𝓞 ℛ₃]
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    (j : ℛ₃ →ₐc[𝓞] ℛ)
    (hexact : RingHom.ker (π : ℛ →ₐ[𝓞] ℛ₁) =
      Ideal.map (j : ℛ₃ →ₐ[𝓞] ℛ) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 ℛ₃)))
    (hff : (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.FaithfullyFlat)
    (hfin : (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.Finite)
    (hL : ∀ z ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge k p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
        Deformation.DieudonneModule.map k p
          (Bialgebra.TensorProduct.map (BialgHom.id k k) π) y = z)
    (hG₁ : ∀ (Y' : Type (max w₁ w')) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
        [Module.Flat 𝓞 Y'] (ψ : TensorProduct 𝓞 k ℛ₁ →ₐ[k] TensorProduct 𝓞 k Y'),
      (∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ₁)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₁)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₁).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₁)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y' →ₐ[𝓞] TensorProduct 𝓞 k Y').toRingHom) →
      ∃ x : ℛ₁ →ₐ[𝓞] Y', Algebra.TensorProduct.map (AlgHom.id k k) x = ψ)
    (hG : ∀ (Y' : Type (max w₁ w')) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
        [Module.Flat 𝓞 Y'] (y y' : ℛ →ₐ[𝓞] Y'),
      Algebra.TensorProduct.map (AlgHom.id k k) y = Algebra.TensorProduct.map (AlgHom.id k k) y' →
        y = y')
    (Y : Type w') [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Flat 𝓞 Y]
    (hG₃ : ∀ ψ : TensorProduct 𝓞 k ℛ₃ →ₐ[k] TensorProduct 𝓞 k Y,
      (∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ₃)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₃)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ₃ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₃).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₃)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) →
      ∃ x : ℛ₃ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = ψ)
    (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈ Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ :=
  exists_algHom_red_eq p hp hk hker π hπ j hexact hff hfin hL
    (fun Y' _ _ _ _ ψ hψ => hG₁ Y' ψ hψ) (fun Y' _ _ _ _ y y' h => hG Y' y y' h)
    (fun ψ hψ => hG₃ ψ hψ) χ hχ

end S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit
end P2MW
export P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit (solution)
