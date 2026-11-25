-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.inv_eq_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:40.189365+00:00
-- url     : https://prove2.me/submissions/176ca61e-8232-436a-a471-d7ae0cdd9a16

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution (hP : IsCayleyU k r ε P) : P⁻¹ = Pᴴ :=
  Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hP.2)
end CompanionTheory.LimBd.Main
