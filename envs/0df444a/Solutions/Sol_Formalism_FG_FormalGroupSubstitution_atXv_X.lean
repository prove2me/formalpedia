-- Prove2me | solution 1 for Formalism.FG.FormalGroupSubstitution.atXv_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:36.450391+00:00
-- url     : https://prove2.me/submissions/70a99e57-d04f-45ae-87a8-fc46fb4d8f3c

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
    Formalism.FG.atXv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vX j := by
  unfold Formalism.FG.atXv
  exact subst_X' _ (fun s => by simp) j
end Formalism.FG.FormalGroupSubstitution
