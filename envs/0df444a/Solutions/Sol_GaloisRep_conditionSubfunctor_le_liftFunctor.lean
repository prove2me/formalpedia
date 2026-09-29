-- Prove2me | solution 1 for GaloisRep.conditionSubfunctor_le_liftFunctor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/24bf7ae3-c735-53d5-8dbc-dbb2ba5163cd

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_conditionSubfunctor_le_liftFunctor

set_option autoImplicit false

open CategoryTheory IsLocalRing

theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField) :
    GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀ ≤
      Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀ :=
  fun _ _ h => h.1

end S_GaloisRep_conditionSubfunctor_le_liftFunctor
end P2MW
export P2MW.S_GaloisRep_conditionSubfunctor_le_liftFunctor (solution)
