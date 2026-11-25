-- Prove2me | solution 1 for CompanionTheory.WaveGrid.cfg_v_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:44.163809+00:00
-- url     : https://prove2.me/submissions/19757a51-56ae-445a-a467-7de4da0a33f4

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
theorem _root_.solution (hok : c.Ok) (i : ℕ) (hi1 : 1 ≤ i) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i ∧ c.v i ≤ c.v 1 := by
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have h1 : (1:ℝ) ≤ i := by exact_mod_cast hi1
  have h2 : (i:ℝ) + 1 ≤ c.k := by exact_mod_cast hi
  simp only [Sz.Cfg.v, Nat.cast_one]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 1 - i)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * c.Del) (by linarith : (0:ℝ) ≤ (i:ℝ) - 1)]
end CompanionTheory.WaveGrid
