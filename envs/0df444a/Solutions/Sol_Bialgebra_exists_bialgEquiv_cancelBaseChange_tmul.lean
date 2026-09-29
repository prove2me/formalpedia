-- Prove2me | solution 1 for Bialgebra.exists_bialgEquiv_cancelBaseChange_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4013d030-c935-5e47-86e7-075aedb1d265

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul

set_option autoImplicit false

open scoped TensorProduct

open Bialgebra in

theorem solution
    (R R' S : Type*) [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] (C : Type*) [CommRing C] [Bialgebra R C] :
    ∃ e : S ⊗[R'] (R' ⊗[R] C) ≃ₐc[S] S ⊗[R] C, ∀ (s : S) (r : R') (c : C), e (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := by
  classical
  let e₀ : S ⊗[R'] (R' ⊗[R] C) ≃ₐ[S] S ⊗[R] C := Algebra.TensorProduct.cancelBaseChange R R' S S C
  have he₀ : ∀ (s : S) (r : R') (c : C), e₀ (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := fun s r c =>
    Algebra.TensorProduct.cancelBaseChange_tmul R R' S S C s r c
  have he₁ : ∀ c : C, e₀ ((1 : S) ⊗ₜ ((1 : R') ⊗ₜ c)) = (1 : S) ⊗ₜ c := fun c => by rw [he₀, one_smul]
  refine ⟨BialgEquiv.ofAlgEquiv e₀ ?_ ?_, he₀⟩
  ·
    apply Algebra.TensorProduct.ext
    · ext
    · apply Algebra.TensorProduct.ext
      · ext
      · ext c
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_algHom, Bialgebra.counitAlgHom_apply]
        rw [he₁]
        simp [TensorProduct.counit_tmul]
  ·
    apply Algebra.TensorProduct.ext
    · ext
    · apply Algebra.TensorProduct.ext
      · ext
      · ext c
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_algHom, Bialgebra.comulAlgHom_apply]
        rw [he₁]

        let 𝓡 := Coalgebra.Repr.arbitrary R c
        have hc : Coalgebra.comul (R := R) c = 𝓡.index.sum fun i => 𝓡.left i ⊗ₜ[R] 𝓡.right i := 𝓡.eq.symm
        simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply, hc, TensorProduct.tmul_sum, map_sum,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [AlgEquiv.coe_algHom, he₁]

end S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul
end P2MW
export P2MW.S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul (solution)
