-- Prove2me | solution 1 for DrinfeldCurve.tateProdRep_quadratic_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6c36dd38-3f1a-579e-a4bf-7e2f124eacd4

import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_tateProdRep_quadratic_of_forall

set_option autoImplicit false

open scoped TensorProduct

open DrinfeldCurve in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] (S : Type)
    (θ : (GaloisField q 2)ˣ →* Eˣ) {W : Type*} [AddCommGroup W] [Module E W]
    (σ : Representation E (CuspidalType.GL2 q) W)
    (hT : ∀ u : W →ₗ[E]
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))),
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q),
        u ∘ₗ σ g = tateRep q k ℓ E ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ hSubgroup q),
        let A : (W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) →
            (W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) :=
          fun v => tateRep q k ℓ E ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Eˣ) : E) + ((θ (α ^ q) : Eˣ) : E)) • A u +
          (((θ α : Eˣ) : E) * ((θ (α ^ q) : Eˣ) : E)) • u = 0) :
    ∀ u : W →ₗ[E] tateProd q k ℓ E S,
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q),
        u ∘ₗ σ g = tateProdRep q k ℓ E S ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ hSubgroup q),
        let A : (W →ₗ[E] tateProd q k ℓ E S) → (W →ₗ[E] tateProd q k ℓ E S) :=
          fun v => tateProdRep q k ℓ E S ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Eˣ) : E) + ((θ (α ^ q) : Eˣ) : E)) • A u +
          (((θ α : Eˣ) : E) * ((θ (α ^ q) : Eˣ) : E)) • u = 0 := by
  intro u hu α g hg
  dsimp only
  refine LinearMap.ext fun w => funext fun s => ?_
  have hus := hT ((LinearMap.proj s).comp u) (fun g' hg₁' => by
      ext w'
      have h := congrArg (fun f : W →ₗ[E] tateProd q k ℓ E S => f w' s) (hu g' hg₁')
      simpa [tateProdRep_apply] using h) α g hg
  have hw := congrArg (fun f : W →ₗ[E]
      (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) => f w) hus
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.zero_apply] at hw
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, tateProdRep_apply]
  exact hw

end S_DrinfeldCurve_tateProdRep_quadratic_of_forall
end P2MW
export P2MW.S_DrinfeldCurve_tateProdRep_quadratic_of_forall (solution)
