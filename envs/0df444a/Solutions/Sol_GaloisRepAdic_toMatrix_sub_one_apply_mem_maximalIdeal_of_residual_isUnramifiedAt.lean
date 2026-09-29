-- Prove2me | solution 1 for GaloisRepAdic.toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/aaafbcaf-6bbf-56f0-8ffe-3abb539d7ec2

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt

set_option autoImplicit false
open IsLocalRing

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (hunr : ρ.residual.IsUnramifiedAt q)
    (b : Module.Basis (Fin 2) A ρ.V) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (i j : Fin 2) :
    LinearMap.toMatrix b b (ρ.ρ σ) i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A := by

  have h1 : (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A) = 1 := hunr P hP σ hσ

  have h2 := LinearMap.toMatrix_baseChange (IsLocalRing.ResidueField A) (ρ.ρ σ) b b
  rw [h1, LinearMap.toMatrix_one] at h2
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.map_apply, IsLocalRing.ResidueField.algebraMap_eq] at h3

  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← h3]
  have h4 : IsLocalRing.residue A ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField A)) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h4, sub_self]

end S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt
end P2MW
export P2MW.S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt (solution)
