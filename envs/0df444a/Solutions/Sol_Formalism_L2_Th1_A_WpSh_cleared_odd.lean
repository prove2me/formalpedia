-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:21:18.0446+00:00
-- url     : https://prove2.me/submissions/e570b91c-1fdc-42ad-be79-3fc3db5ebaa8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_unique
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution [CharZero K] {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) (n : ℕ)
    (hn : Odd n) : coeff n r = 0 := by
  have e := cleared_unique (cleared_neg h) h
  have e1 := congrArg (coeff n) e
  rw [coeff_rescale, hn.neg_one_pow] at e1
  have e2 : (2 : K) * coeff n r = 0 := by linear_combination (-1 : K) * e1
  exact (mul_eq_zero.mp e2).resolve_left two_ne_zero
end Formalism.L2.Th1.A.WpSh
