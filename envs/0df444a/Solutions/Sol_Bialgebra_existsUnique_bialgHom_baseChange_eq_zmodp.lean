-- Prove2me | solution 1 for Bialgebra.existsUnique_bialgHom_baseChange_eq_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a6039e1a-5b24-556d-b1aa-e62d2f268f41

import Mathlib
import Theorems.Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
import Theorems.Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace BialgLiftE96

theorem mem_span_of_one_tmul_eq_zero {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
    (hk : Function.Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (T : Type*) [CommRing T] [Algebra 𝓞 T] (x : T) (hx : (1 : ZMod p) ⊗ₜ[𝓞] x = 0) :
    x ∈ Ideal.span {(p : T)} := by
  set I : Ideal 𝓞 := Ideal.span {(p : 𝓞)} with hI
  have hker' : RingHom.ker (Algebra.ofId 𝓞 (ZMod p) : 𝓞 →+* ZMod p) = I := hker
  let e₀ : (𝓞 ⧸ RingHom.ker (Algebra.ofId 𝓞 (ZMod p) : 𝓞 →+* ZMod p)) ≃ₐ[𝓞] ZMod p :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId 𝓞 (ZMod p)) hk
  let e₁ : ZMod p ≃ₐ[𝓞] 𝓞 ⧸ I := e₀.symm.trans (Ideal.quotientEquivAlgOfEq 𝓞 hker')
  let e₂ : ZMod p ⊗[𝓞] T ≃ₐ[𝓞] (𝓞 ⧸ I) ⊗[𝓞] T := Algebra.TensorProduct.congr e₁ AlgEquiv.refl
  let e₃ : (𝓞 ⧸ I) ⊗[𝓞] T ≃ₗ[𝓞] T ⧸ (I • ⊤ : Submodule 𝓞 T) := TensorProduct.quotTensorEquivQuotSMul T I
  have h1 : e₂ ((1 : ZMod p) ⊗ₜ[𝓞] x) = (1 : 𝓞 ⧸ I) ⊗ₜ[𝓞] x := by
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]; rfl
  have h2 : e₃ ((1 : 𝓞 ⧸ I) ⊗ₜ[𝓞] x) = Submodule.Quotient.mk x := by
    rw [← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h3 : (Submodule.Quotient.mk x : T ⧸ (I • ⊤ : Submodule 𝓞 T)) = 0 := by
    rw [← h2, ← h1, hx, map_zero, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at h3
  rw [hI, Ideal.map_span, Set.image_singleton, map_natCast] at h3
  exact h3

section tensor

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
  (L : Type w) [CommRing L] [Algebra 𝓞 L]

noncomputable def Θ : (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L) →ₐ[ZMod p] ZMod p ⊗[𝓞] (L ⊗[𝓞] L) :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (Algebra.TensorProduct.includeLeft (S := 𝓞) : L →ₐ[𝓞] L ⊗[𝓞] L))
    (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L))

theorem Θ_tmul (s s' : ZMod p) (l l' : L) :
    Θ p L ((s ⊗ₜ[𝓞] l) ⊗ₜ[ZMod p] (s' ⊗ₜ[𝓞] l')) = (s * s') ⊗ₜ[𝓞] (l ⊗ₜ[𝓞] l') := by
  simp [Θ, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.tmul_mul_tmul]

end tensor

end BialgLiftE96

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Bialgebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    [Algebra.FormallyEtale 𝓞 H]
    (L : Type w) [CommRing L] [Bialgebra 𝓞 L] [Module.Free 𝓞 L] [Module.Finite 𝓞 L]
    (φbar : (ZMod p ⊗[𝓞] H) →ₐc[ZMod p] (ZMod p ⊗[𝓞] L)) :
    ∃! φ : H →ₐc[𝓞] L,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ : H →ₐ[𝓞] L) =
        (φbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] L) := by
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _

  obtain ⟨ψ, hψ, huniq⟩ := Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
    p hp hker H L (φbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] L)
  have hψ1 : ∀ h : H, (φbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] L) ((1 : ZMod p) ⊗ₜ[𝓞] h)
      = (1 : ZMod p) ⊗ₜ[𝓞] ψ h := by
    intro h
    rw [← hψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hψ1' : ∀ h : H, φbar ((1 : ZMod p) ⊗ₜ[𝓞] h) = (1 : ZMod p) ⊗ₜ[𝓞] ψ h := hψ1

  have hcounit : (Bialgebra.counitAlgHom 𝓞 L).comp ψ = Bialgebra.counitAlgHom 𝓞 H := by
    apply AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified (Ideal.span {(p : 𝓞)})
      (IsAdicComplete.le_jacobson_bot _)
    intro h
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have e1 := congrArg (fun F => F ((1 : ZMod p) ⊗ₜ[𝓞] h))
      (CoalgHomClass.counit_comp (φbar : ZMod p ⊗[𝓞] H →ₐc[ZMod p] ZMod p ⊗[𝓞] L))
    simp only [LinearMap.coe_comp, Function.comp_apply] at e1
    change Coalgebra.counit (φbar ((1 : ZMod p) ⊗ₜ[𝓞] h)) = Coalgebra.counit ((1 : ZMod p) ⊗ₜ[𝓞] h) at e1
    rw [hψ1', TensorProduct.counit_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at e1
    exact e1

  have hcomul : (Algebra.TensorProduct.map ψ ψ).comp (Bialgebra.comulAlgHom 𝓞 H) = (Bialgebra.comulAlgHom 𝓞 L).comp ψ := by
    haveI : IsAdicComplete (Ideal.span {(p : L ⊗[𝓞] L)}) (L ⊗[𝓞] L) :=
      IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (L ⊗[𝓞] L)
    apply AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified (Ideal.span {(p : L ⊗[𝓞] L)})
      (IsAdicComplete.le_jacobson_bot _)
    intro h
    apply BialgLiftE96.mem_span_of_one_tmul_eq_zero p hk hker (L ⊗[𝓞] L)
    rw [TensorProduct.tmul_sub, sub_eq_zero]

    have e2 := congrArg (fun F => F ((1 : ZMod p) ⊗ₜ[𝓞] h))
      (CoalgHomClass.map_comp_comul (φbar : ZMod p ⊗[𝓞] H →ₐc[ZMod p] ZMod p ⊗[𝓞] L))
    simp only [LinearMap.coe_comp, Function.comp_apply] at e2
    change TensorProduct.map _ _ (Coalgebra.comul ((1 : ZMod p) ⊗ₜ[𝓞] h)) =
      Coalgebra.comul (φbar ((1 : ZMod p) ⊗ₜ[𝓞] h)) at e2
    rw [hψ1', TensorProduct.comul_tmul, TensorProduct.comul_tmul, CommSemiring.comul_apply] at e2

    have LA : ∀ c : L ⊗[𝓞] L, BialgLiftE96.Θ p L
        (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm 𝓞 (ZMod p) 𝓞 (ZMod p) (ZMod p) (ZMod p) L L
          (((1 : ZMod p) ⊗ₜ[ZMod p] (1 : ZMod p)) ⊗ₜ[𝓞] c)) = (1 : ZMod p) ⊗ₜ[𝓞] c := by
      intro c
      induction c using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, TensorProduct.tmul_zero]
      | tmul l l' =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, BialgLiftE96.Θ_tmul, one_mul]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, TensorProduct.tmul_add]
    have LB : ∀ c : H ⊗[𝓞] H, BialgLiftE96.Θ p L (TensorProduct.map
        ((φbar : ZMod p ⊗[𝓞] H →ₐc[ZMod p] ZMod p ⊗[𝓞] L) : ZMod p ⊗[𝓞] H →ₗ[ZMod p] ZMod p ⊗[𝓞] L)
        ((φbar : ZMod p ⊗[𝓞] H →ₐc[ZMod p] ZMod p ⊗[𝓞] L) : ZMod p ⊗[𝓞] H →ₗ[ZMod p] ZMod p ⊗[𝓞] L)
        (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm 𝓞 (ZMod p) 𝓞 (ZMod p) (ZMod p) (ZMod p) H H
          (((1 : ZMod p) ⊗ₜ[ZMod p] (1 : ZMod p)) ⊗ₜ[𝓞] c))) = (1 : ZMod p) ⊗ₜ[𝓞] (Algebra.TensorProduct.map ψ ψ c) := by
      intro c
      induction c using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero, map_zero, TensorProduct.tmul_zero]
      | tmul h₁ h₂ =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul]
        change BialgLiftE96.Θ p L (φbar ((1 : ZMod p) ⊗ₜ[𝓞] h₁) ⊗ₜ[ZMod p] φbar ((1 : ZMod p) ⊗ₜ[𝓞] h₂)) = _
        rw [hψ1', hψ1', BialgLiftE96.Θ_tmul, one_mul, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add, TensorProduct.tmul_add]
    have e3 := congrArg (BialgLiftE96.Θ p L) e2
    rw [LB, LA] at e3
    exact e3

  let φ : H →ₐc[𝓞] L := BialgHom.ofAlgHom ψ hcounit hcomul
  have hφ : (φ : H →ₐ[𝓞] L) = ψ := rfl
  refine ⟨φ, ?_, fun φ' hφ' => ?_⟩
  · show Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ : H →ₐ[𝓞] L) = _
    exact hψ
  · exact BialgHom.coe_algHom_injective ((huniq (φ' : H →ₐ[𝓞] L) hφ').trans hφ.symm)

end S_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp
end P2MW
export P2MW.S_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp (solution)
