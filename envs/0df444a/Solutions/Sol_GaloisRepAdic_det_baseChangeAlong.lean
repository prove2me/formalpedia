-- Prove2me | solution 1 for GaloisRepAdic.det_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/531c842c-d815-5bcb-aec6-fb813ce9ffb1

import Definitions.Def_GaloisRep_Adic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_det_baseChangeAlong

theorem solution {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ((ρ.baseChangeAlong φ hφ).det σ : B) = φ (ρ.det σ : A) := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = φ (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)

end S_GaloisRepAdic_det_baseChangeAlong
end P2MW
export P2MW.S_GaloisRepAdic_det_baseChangeAlong (solution)
