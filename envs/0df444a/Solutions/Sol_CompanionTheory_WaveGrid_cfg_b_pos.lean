-- Prove2me | solution 1 for CompanionTheory.WaveGrid.cfg_b_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:44.170327+00:00
-- url     : https://prove2.me/submissions/40fd0a1f-0848-491a-a084-00ec3d8a65d4

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
theorem _root_.solution (hok : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact hok.hb1
  | succ n hn ih =>
    intro hnm
    have h1 := hok.hgap n hn (by omega)
    have h2 := ih (by omega)
    linarith
end CompanionTheory.WaveGrid
