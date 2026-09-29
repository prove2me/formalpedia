-- Prove2me | solution 1 for GaloisRepAdic.charpoly_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8deae6e8-793d-5089-9e42-494fc1da50b3

import Definitions.Def_GaloisRep_Adic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_charpoly_baseChangeAlong

open Polynomial

theorem solution {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ := by
  letI : Algebra A B := φ.toAlgebra
  exact LinearMap.charpoly_baseChange (ρ.ρ σ) B

end S_GaloisRepAdic_charpoly_baseChangeAlong
end P2MW
export P2MW.S_GaloisRepAdic_charpoly_baseChangeAlong (solution)
