-- Prove2me | solution 1 for Formalism.FG.FormalGroupSubstitution.atYv_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:36.513671+00:00
-- url     : https://prove2.me/submissions/8454dafb-ef11-4abf-94bc-b5aeca81fa79

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample
import Theorems.Thm_P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupSubstitution
open MvPowerSeries
namespace Formalism.FG.FormalGroupSubstitution
theorem _root_.solution (j : Fin 2) :
    Formalism.FG.atYv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vY j := by
  unfold Formalism.FG.atYv
  exact subst_X' _ (fun s => by simp) j
end Formalism.FG.FormalGroupSubstitution
