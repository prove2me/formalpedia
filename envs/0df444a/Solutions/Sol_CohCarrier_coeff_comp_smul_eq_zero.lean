-- Prove2me | solution 1 for CohCarrier.coeff_comp_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/148d1c36-7f3d-5c9d-a962-0d014ab3624c

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_coeff_comp_smul_eq_zero

set_option autoImplicit false

open CohCarrier

theorem solution (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] {R : Type*} [Semiring R] [Module R A] (g : A →+ B) (ϖ : R)
    (hg : ∀ a : A, g (ϖ • a) = 0) (φ : H1 M H A) :
    g.comp (ϖ • φ) = 0 := by
  ext x
  show g ((ϖ • φ) x) = 0
  rw [AddMonoidHom.smul_apply, hg]

end S_CohCarrier_coeff_comp_smul_eq_zero
end P2MW
export P2MW.S_CohCarrier_coeff_comp_smul_eq_zero (solution)
