-- Prove2me | solution 1 for GaloisRepAdic.isEquiv_baseChangeAlong_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/57ef3a0e-cdc7-57ed-ad49-626020fd57a7

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong

set_option autoImplicit false
open scoped TensorProduct

namespace BCBCAProof

theorem aux
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : C ⊗[B] (B ⊗[A] ρ.V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
        (LinearMap.baseChange C (LinearMap.baseChange B (ρ.ρ σ)) x) =
      LinearMap.baseChange C (ρ.ρ σ) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

end BCBCAProof

theorem solution
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (f : A →+* B) (hf : IsLocalHom f) (g : B →+* C) (hg : IsLocalHom g) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong f hf).baseChangeAlong g hg).IsEquiv
      (ρ.baseChangeAlong (g.comp f) (RingHom.isLocalHom_comp g f)) := by
  classical
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
            map_apply := ?_ }⟩
  intro σ x
  exact BCBCAProof.aux ρ σ x

end S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong
end P2MW
export P2MW.S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong (solution)
