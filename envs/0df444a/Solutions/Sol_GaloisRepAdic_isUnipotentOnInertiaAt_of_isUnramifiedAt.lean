-- Prove2me | solution 1 for GaloisRepAdic.isUnipotentOnInertiaAt_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ea8d04bf-0770-5f53-8f58-21ee6f485406

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt

set_option autoImplicit false

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ}
    (h : ρ.IsUnramifiedAt q) : ρ.IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  rw [h P hP σ hσ, LinearMap.charpoly_one, ρ.finrank_eq]

end S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt
end P2MW
export P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt (solution)
