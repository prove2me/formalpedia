-- Prove2me | solution 1 for DrinfeldCurve.exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/463d65e5-3aa5-5657-8003-28c15a55f5f9

import Definitions.Def_DrinfeldCurve_TateRep
import Theorems.Thm_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv
import Theorems.Thm_AlgebraicCurve_Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
import Theorems.Thm_TateModule_exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv

set_option autoImplicit false

open scoped TensorProduct
open DrinfeldCurve

set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (k' : Type) [Field k'] [Algebra (GaloisField q 2) k'] [IsDomain (DrinfeldCurve.CoordRing q k')]
    (e : k ≃ₐ[GaloisField q 2] k')
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (S : Type) :
    ∃ Θ : DrinfeldCurve.tateProd q k ℓ E S ≃ₗ[E] DrinfeldCurve.tateProd q k' ℓ E S,
      ∀ h : DrinfeldCurve.hSubgroup q,
        (Θ : DrinfeldCurve.tateProd q k ℓ E S →ₗ[E] DrinfeldCurve.tateProd q k' ℓ E S) ∘ₗ
            DrinfeldCurve.tateProdRep q k ℓ E S h =
          DrinfeldCurve.tateProdRep q k' ℓ E S h ∘ₗ
            (Θ : DrinfeldCurve.tateProd q k ℓ E S →ₗ[E] DrinfeldCurve.tateProd q k' ℓ E S) := by
  classical

  obtain ⟨φ, hφk, -, -, hφH⟩ :=
    DrinfeldCurve.exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv q k k' e

  obtain ⟨Φ, Ψ, -, -, hΨ⟩ :=
    AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv (K := k) (K' := k')
      (F := drinfeldFunctionField q k) (F' := drinfeldFunctionField q k') (e : k ≃+* k') φ (fun a => hφk a)

  obtain ⟨Θ₀, -, hΘ₀⟩ :=
    TateModule.exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv ℓ Ψ
      (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)
      (drinfeldFunctionField q k' ≃ₐ[k'] drinfeldFunctionField q k')
  have hΨh : ∀ (h : hSubgroup q) (x : AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)),
      Ψ (hFunctionFieldAction q k h • x) = hFunctionFieldAction q k' h • Ψ x :=
    fun h => hΨ (hFunctionFieldAction q k h) (hFunctionFieldAction q k' h) (hφH h)
  have hnat := fun h : hSubgroup q =>
    hΘ₀ (hFunctionFieldAction q k h) (hFunctionFieldAction q k' h) (hΨh h)

  set P := (Θ₀ : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]]
      ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k'))).baseChange E with hP
  set Q := (Θ₀.symm : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k')) →ₗ[ℚ_[ℓ]]
      ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))).baseChange E with hQ
  have hQP : Q ∘ₗ P = LinearMap.id := by
    rw [hP, hQ, ← LinearMap.baseChange_comp]
    have : (Θ₀.symm : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k')) →ₗ[ℚ_[ℓ]]
          ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) ∘ₗ
        (Θ₀ : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k'))) =
        LinearMap.id := LinearMap.ext fun x => Θ₀.symm_apply_apply x
    rw [this, LinearMap.baseChange_id]
  have hPQ : P ∘ₗ Q = LinearMap.id := by
    rw [hP, hQ, ← LinearMap.baseChange_comp]
    have : (Θ₀ : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k'))) ∘ₗ
        (Θ₀.symm : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k')) →ₗ[ℚ_[ℓ]]
          ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) = LinearMap.id := LinearMap.ext fun x => Θ₀.apply_symm_apply x
    rw [this, LinearMap.baseChange_id]
  let ΘE : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) ≃ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k'))) := LinearEquiv.ofLinear P Q hPQ hQP
  have htr : ∀ h, DrinfeldCurve.tateRep q k ℓ E h =
      (ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)) (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) (hFunctionFieldAction q k h)).baseChange E :=
    fun h => rfl
  have htr' : ∀ h, DrinfeldCurve.tateRep q k' ℓ E h =
      (ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k' (drinfeldFunctionField q k')) (drinfeldFunctionField q k' ≃ₐ[k'] drinfeldFunctionField q k') (hFunctionFieldAction q k' h)).baseChange E :=
    fun h => rfl
  have hE : ∀ h, P ∘ₗ DrinfeldCurve.tateRep q k ℓ E h = DrinfeldCurve.tateRep q k' ℓ E h ∘ₗ P := fun h => by
    rw [htr, htr', hP, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hnat]

  refine ⟨LinearEquiv.piCongrRight fun _ : S => ΘE, fun h => ?_⟩
  apply LinearMap.ext; intro v; funext s
  show ΘE (DrinfeldCurve.tateProdRep q k ℓ E S h v s) = DrinfeldCurve.tateRep q k' ℓ E h (ΘE (v s))
  rw [DrinfeldCurve.tateProdRep_apply]
  exact congrArg (fun f => f (v s)) (hE h)

end S_DrinfeldCurve_exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv
end P2MW
export P2MW.S_DrinfeldCurve_exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv (solution)
