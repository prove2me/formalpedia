-- Prove2me | solution 1 for Formalism.L2.Th1.A.plusChord_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:10.227008+00:00
-- url     : https://prove2.me/submissions/8484437e-9d73-472b-bff6-936f13d28e58

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_chord
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_chord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord


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
open Plus
namespace Formalism.L2.Th1.A
theorem _root_.solution (hFL : FlowL.{u}) : PlusChord.{u} := by
  intro R _ W xP yP hP
  exact Plus.chord W hFL hP
end Formalism.L2.Th1.A
