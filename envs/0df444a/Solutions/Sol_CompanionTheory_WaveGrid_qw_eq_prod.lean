-- Prove2me | solution 1 for CompanionTheory.WaveGrid.qw_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:59.644026+00:00
-- url     : https://prove2.me/submissions/a5b97d02-6323-4327-9e69-958eb2c9ec1d

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt
namespace CompanionTheory.WaveGrid
theorem _root_.solution {S : Type} [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (L : List (Wd.Letter ℂ S)) (Y : ℂ) :
    Wd.qw q L Y = q Y * (L.map fun l => facW l Y).prod := by
  induction L with
  | nil => simp [Wd.qw]
  | cons l L ih =>
    by_cases h : l.plus
    · simp only [Wd.qw, h, if_true, List.map_cons, List.prod_cons, ih, facW]
      ring
    · simp only [Wd.qw, h, List.map_cons, List.prod_cons, ih, facW]
      simp only [Bool.false_eq_true, if_false]
      ring
end CompanionTheory.WaveGrid
