-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q2.subst_neg_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:24.735695+00:00
-- url     : https://prove2.me/submissions/e38d4eb8-2091-4cee-941a-259e35c8228d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Q2
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.Q2
theorem _root_.solution (f : R⟦X⟧) : f.subst (-X : R⟦X⟧) = rescale (-1) f := by
  rw [PowerSeries.rescale_eq_subst, neg_one_smul]
end Formalism.L2.Th1.A.Q2
