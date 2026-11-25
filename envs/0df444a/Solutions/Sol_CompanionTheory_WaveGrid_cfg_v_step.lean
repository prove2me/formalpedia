-- Prove2me | solution 1 for CompanionTheory.WaveGrid.cfg_v_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:08.686006+00:00
-- url     : https://prove2.me/submissions/889ed1fd-b1fc-41c1-b4ad-b97d7c3ed930

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
variable (c : Sz.Cfg)
namespace CompanionTheory.WaveGrid
theorem _root_.solution (i : ℕ) : c.v i = c.v (i + 1) + 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring
end CompanionTheory.WaveGrid
