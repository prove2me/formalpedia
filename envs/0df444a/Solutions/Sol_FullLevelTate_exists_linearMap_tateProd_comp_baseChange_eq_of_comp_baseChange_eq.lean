-- Prove2me | solution 1 for FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8533e020-977f-54d2-8504-77374f7f45e6

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq

set_option autoImplicit false

open scoped TensorProduct

private theorem FullLevelTate.exists_linearMap_pi_comp_baseChange_eq_of_comp_baseChange_eq_aux
    {Z Q O' K : Type} [CommRing Z] [CommRing Q] [Algebra Z Q] [CommRing O'] [Algebra Z O'] [CommRing K]
    [Algebra O' K] [Algebra Q K]
    (hOK : ∀ z : Z, algebraMap O' K (algebraMap Z O' z) = algebraMap Q K (algebraMap Z Q z))
    {T : Type} [AddCommGroup T] [Module Z T] {V : Type} [AddCommGroup V] [Module Q V] {ι : Type}
    (sp₀ : Q ⊗[Z] T →ₗ[Q] (ι → Q ⊗[Q] V)) :
    ∃ sp : K ⊗[O'] (O' ⊗[Z] T) →ₗ[K] (ι → K ⊗[Q] V),
      (∀ (c : K) (a : O') (x : T) (i : ι),
        sp (c ⊗ₜ[O'] (a ⊗ₜ[Z] x)) i =
          (algebraMap O' K a * c) ⊗ₜ[Q] TensorProduct.lid Q V (sp₀ ((1 : Q) ⊗ₜ[Z] x) i)) ∧
      ∀ (A : Module.End Z T) (B : Module.End Q V) (A' : Module.End O' (O' ⊗[Z] T)),
        (∀ (a : O') (x : T), A' (a ⊗ₜ[Z] x) = a ⊗ₜ[Z] A x) →
        sp₀ ∘ₗ A.baseChange Q = (LinearMap.pi fun s => (B.baseChange Q).comp (LinearMap.proj s)) ∘ₗ sp₀ →
          sp ∘ₗ A'.baseChange K = (LinearMap.pi fun s => (B.baseChange K).comp (LinearMap.proj s)) ∘ₗ sp := by
  classical

  letI algZK : Algebra Z K := ((algebraMap O' K).comp (algebraMap Z O')).toAlgebra
  haveI towZO' : IsScalarTower Z O' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towZQ : IsScalarTower Z Q K := IsScalarTower.of_algebraMap_eq fun z => hOK z

  have keyT : ∀ (r : Q) (x : T), r ⊗ₜ[Z] x = r • ((1 : Q) ⊗ₜ[Z] x) := fun r x => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have keyV : ∀ (r : Q) (y : V), (1 : K) ⊗ₜ[Q] (r • y) = algebraMap Q K r ⊗ₜ[Q] y := fun r y => by
    rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  have h1 : ∀ (z : Z) (x : T), (1 : Q) ⊗ₜ[Z] (z • x) = algebraMap Z Q z • ((1 : Q) ⊗ₜ[Z] x) := fun z x => by
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, keyT]

  let ψ : T →ₗ[Z] (ι → K ⊗[Q] V) :=
    { toFun := fun x i => (1 : K) ⊗ₜ[Q] TensorProduct.lid Q V (sp₀ ((1 : Q) ⊗ₜ[Z] x) i)
      map_add' := fun x y => by
        funext i
        simp only [Pi.add_apply, TensorProduct.tmul_add, LinearMap.map_add, LinearEquiv.map_add]
      map_smul' := fun z x => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [h1, LinearMap.map_smul, Pi.smul_apply, LinearEquiv.map_smul, keyV, ← hOK, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_one]
        rfl }
  have ψ_apply : ∀ (x : T) (i : ι), ψ x i = (1 : K) ⊗ₜ[Q] TensorProduct.lid Q V (sp₀ ((1 : Q) ⊗ₜ[Z] x) i) :=
    fun _ _ => rfl

  let sp : K ⊗[O'] (O' ⊗[Z] T) →ₗ[K] (ι → K ⊗[Q] V) := (ψ.liftBaseChange O').liftBaseChange K

  have hsp : ∀ (c : K) (a : O') (x : T) (i : ι), sp (c ⊗ₜ[O'] (a ⊗ₜ[Z] x)) i =
      (algebraMap O' K a * c) ⊗ₜ[Q] TensorProduct.lid Q V (sp₀ ((1 : Q) ⊗ₜ[Z] x) i) := by
    intro c a x i
    simp only [sp, LinearMap.liftBaseChange_tmul]
    rw [Pi.smul_apply, Pi.smul_apply, ψ_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      Algebra.smul_def a (1 : K), mul_one, smul_eq_mul, mul_comm]
  refine ⟨sp, hsp, fun A B A' hA' h0 => ?_⟩

  apply TensorProduct.AlgebraTensorModule.ext
  intro c m
  induction m using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, LinearMap.map_zero]
  | add u v hu hv => simp only [TensorProduct.tmul_add, LinearMap.map_add, hu, hv]
  | tmul a x =>
    have hx := LinearMap.congr_fun h0 ((1 : Q) ⊗ₜ[Z] x)
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at hx
    funext i
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, hA', LinearMap.pi_apply, LinearMap.proj_apply]
    rw [hsp, hsp, hx, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

    generalize sp₀ ((1 : Q) ⊗ₜ[Z] x) i = w
    induction w using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.tmul_zero]
    | add u v hu hv => simp only [LinearMap.map_add, LinearEquiv.map_add, TensorProduct.tmul_add, hu, hv]
    | tmul r y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul,
        LinearMap.map_smul]

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (R : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hR : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : O')
      (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      R σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGal q M' lam σ x)
    (G : CuspidalType.GL2 q →* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hG : ∀ (g : CuspidalType.GL2 q) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      G g (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGL2 q M' lam g x)
    (K : Type) [Field K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)] (index : Type)
    (sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
      DrinfeldCurve.tateProd q k lam ℚ_[lam] index) :
    ∃ sp : K ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')) →ₗ[K]
        DrinfeldCurve.tateProd q k lam K index,
      (∀ (c : K) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (i : index),
        sp (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) i =
          (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] TensorProduct.lid ℚ_[lam] _ (sp₀ ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) i)) ∧
      ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CuspidalType.GL2 q) (α : (GaloisField q 2)ˣ)
          (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
        sp₀ ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g * ModularCurve.FullLevel.tateGal q M' lam τ).baseChange
              ℚ_[lam] = DrinfeldCurve.tateProdRep q k lam ℚ_[lam] index ⟨(g, α), hg⟩ ∘ₗ sp₀ →
          sp ∘ₗ ((G g * R τ).baseChange K) = DrinfeldCurve.tateProdRep q k lam K index ⟨(g, α), hg⟩ ∘ₗ sp := by
  obtain ⟨sp, hsp, hlaw⟩ :=
    FullLevelTate.exists_linearMap_pi_comp_baseChange_eq_of_comp_baseChange_eq_aux (O' := O') (K := K) hOK sp₀
  refine ⟨sp, hsp, fun τ g α hg h0 => ?_⟩
  exact hlaw (ModularCurve.FullLevel.tateGL2 q M' lam g * ModularCurve.FullLevel.tateGal q M' lam τ)
    ((ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
        (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)).comp
      (DrinfeldCurve.hFunctionFieldAction q k) ⟨(g, α), hg⟩)
    (G g * R τ) (fun a x => by rw [Module.End.mul_apply, Module.End.mul_apply, hR, hG]) h0

end S_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq
end P2MW
export P2MW.S_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq (solution)
