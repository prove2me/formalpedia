-- Prove2me | solution 1 for CompanionTheory.WaveGrid.cfg_v_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:53.936044+00:00
-- url     : https://prove2.me/submissions/ffeee258-8678-4f4e-a61c-e90f00aa5eb3

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
theorem _root_.solution (hk : 1 ≤ c.k) : c.v (c.k - 1) = c.vlast := by
  simp only [Sz.Cfg.v, Nat.cast_sub hk, Nat.cast_one]
  ring
end CompanionTheory.WaveGrid
