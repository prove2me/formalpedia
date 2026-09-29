-- Prove2me | solution 1 for CerednikDrinfeld.QM.trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/df609592-fcf6-5963-88a6-430638774bfe

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
import Theorems.Thm_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open QuaternionAlgebra
open scoped Quaternion

namespace C5QuadAlg

theorem quat_sq_eq {a b : ℚ} (m : ℍ[ℚ, a, b]) (n ν : ℤ)
    (hn : m + Star.star m = ((n : ℚ) : ℍ[ℚ, a, b])) (hν : m * Star.star m = ((ν : ℚ) : ℍ[ℚ, a, b])) :
    m * m = (n : ℤ) • m - (ν : ℤ) • (1 : ℍ[ℚ, a, b]) := by
  have hstar : Star.star m = ((n : ℚ) : ℍ[ℚ, a, b]) - m := eq_sub_of_add_eq' hn
  have h2 := hν
  rw [hstar, mul_sub, QuaternionAlgebra.mul_coe_eq_smul] at h2

  have key : m * m = (n : ℚ) • m - ((ν : ℚ) : ℍ[ℚ, a, b]) := by rw [← h2, sub_sub_cancel]
  rw [key, Int.cast_smul_eq_zsmul]
  congr 1
  rw [zsmul_eq_mul, mul_one]
  norm_cast

theorem quat_sq_mem {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ↥Λ) (n ν : ℤ)
    (hn : (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    (hν : (m : ℍ[ℚ, a, b]) * Star.star (m : ℍ[ℚ, a, b]) = ((ν : ℚ) : ℍ[ℚ, a, b])) :
    (m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [quat_sq_eq _ n ν hn hν]
  exact Λ.sub_mem (Λ.smul_mem n m.2) (Λ.smul_mem ν hone)

theorem end_quad {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] (Φ : Module.End k V) (n ν : ℤ)
    (h : Φ * Φ = (n : ℤ) • Φ - (ν : ℤ) • (1 : Module.End k V)) :
    Φ * Φ - ((n : ℤ) : k) • Φ + ((ν : ℤ) : k) • (1 : Module.End k V) = 0 := by
  rw [h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  abel

theorem addHom_comb {M N : Type*} [AddCommGroup M] [AddCommGroup N] (θ : M → N) (hθ : ∀ x y, θ (x + y) = θ x + θ y)
    (x y : M) (n ν : ℤ) : θ (n • x - ν • y) = n • θ x - ν • θ y := by
  let θh : M →+ N := AddMonoidHom.mk' θ hθ
  change θh (n • x - ν • y) = n • θh x - ν • θh y
  rw [map_sub, map_zsmul, map_zsmul]

end C5QuadAlg

namespace C5Quad

open Matrix

theorem matrix_fin_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (n N : R)
    (hM : M * M - n • M + N • (1 : Matrix (Fin 2) (Fin 2) R) = 0) :
    (M.trace - n) * ((M.trace - n) ^ 2 - (n ^ 2 - 4 * N)) = 0 := by
  have h := fun i j => congrFun (congrFun hM i) j
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_two, Matrix.zero_apply,
    smul_eq_mul, Fin.isValue, if_true, if_false, one_ne_zero, zero_ne_one] at h00 h01 h10 h11
  rw [Matrix.trace_fin_two]
  linear_combination (3 * (M 0 0 + M 1 1 - n) - 2 * M 0 0 + n) * h00 +
    (M 0 0 + M 1 1 - n + 2 * M 0 0 - n) * h11 - 4 * M 0 1 * h10

theorem trace_sub_mul_sq_sub_eq_zero {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V = 2) (A : Module.End k V) (n N : k)
    (hA : A * A - n • A + N • (1 : Module.End k V) = 0) :
    (LinearMap.trace k V A - n) * ((LinearMap.trace k V A - n) ^ 2 - (n ^ 2 - 4 * N)) = 0 := by
  classical
  let b := Module.finBasisOfFinrankEq k V hV
  have htr : LinearMap.trace k V A = (LinearMap.toMatrix b b A).trace := LinearMap.trace_eq_matrix_trace k b A
  have hM : LinearMap.toMatrix b b A * LinearMap.toMatrix b b A - n • LinearMap.toMatrix b b A +
      N • (1 : Matrix (Fin 2) (Fin 2) k) = 0 := by
    have := congrArg (LinearMap.toMatrix b b) hA
    simpa [LinearMap.toMatrix_mul, map_sub, map_add, LinearMap.toMatrix_one] using this
  rw [htr]
  exact matrix_fin_two _ n N hM

end C5Quad

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    [SmoothOfRelativeDimension 2 f]
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : ↥Λ) (Φ : V →ₗ[k] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v))
    (n ν : ℤ) (hn : (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    (hν : (m : ℍ[ℚ, a, b]) * Star.star (m : ℍ[ℚ, a, b]) = ((ν : ℚ) : ℍ[ℚ, a, b])) :
    (LinearMap.trace k V Φ - (n : k)) * ((LinearMap.trace k V Φ - (n : k)) ^ 2 - ((n : k) ^ 2 - 4 * (ν : k))) = 0 := by
  have hV : Module.finrank k V = 2 :=
    CerednikDrinfeld.QM.finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension L 2 k sk V τ hinj hrange hadd hsmul
  obtain ⟨θ, hθτ, hθadd, hθone, hθmul, hθΦ⟩ :=
    CerednikDrinfeld.QM.exists_moduleEnd_apply_eq_pushPt_of_isTangentVector L act act_over act_hom act_one act_mul act_add
      k sk V τ hinj hrange hadd hsmul
  have hΦθ : θ m = Φ := hθΦ m Φ hΦ
  have hmem : (m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := C5QuadAlg.quat_sq_mem Λ hone m n ν hn hν
  have hθmm : θ ⟨_, hmem⟩ = θ m * θ m := hθmul m m hmem
  have hsub : (⟨_, hmem⟩ : ↥Λ) = (n : ℤ) • m - (ν : ℤ) • (⟨1, hone⟩ : ↥Λ) := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul]
    exact C5QuadAlg.quat_sq_eq _ n ν hn hν
  have hcomb : θ ⟨_, hmem⟩ = (n : ℤ) • θ m - (ν : ℤ) • θ ⟨1, hone⟩ := by
    rw [hsub]; exact C5QuadAlg.addHom_comb θ hθadd m ⟨1, hone⟩ n ν
  rw [hθone hone, hΦθ] at hcomb
  rw [hΦθ] at hθmm
  have hA : Φ * Φ - ((n : ℤ) : k) • Φ + ((ν : ℤ) : k) • (1 : Module.End k V) = 0 :=
    C5QuadAlg.end_quad Φ n ν (hθmm.symm.trans hcomb)
  exact C5Quad.trace_sub_mul_sq_sub_eq_zero hV Φ (n : k) (ν : k) hA

end S_CerednikDrinfeld_QM_trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two
end P2MW
export P2MW.S_CerednikDrinfeld_QM_trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two (solution)
