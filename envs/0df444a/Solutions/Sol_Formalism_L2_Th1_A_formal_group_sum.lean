-- Prove2me | solution 1 for Formalism.L2.Th1.A.formal_group_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:28.55646+00:00
-- url     : https://prove2.me/submissions/6a46c6c0-102f-4774-a7f7-5421ec2f2996

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_formal_group_eq_w_series
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_chord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord
import Theorems.Thm_Formalism_ELL_wSubstUnique


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
namespace Formalism.L2.Th1.A
theorem _root_.solution : FglSum.{u} := by
  intro K _ W
  rw [Fgl1.formal_group_eq_w_series]
  exact Formalism.ELL.WeierstrassChordSeries.chord Formalism.ELL.wSubstUnique (Fgl1.wSer_fixed W)
end Formalism.L2.Th1.A
