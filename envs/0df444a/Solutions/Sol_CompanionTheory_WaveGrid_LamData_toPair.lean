-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LamData.toPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:35.744798+00:00
-- url     : https://prove2.me/submissions/d4fa5bab-382d-49fa-8a22-016f39767fb7

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_pairOK_of_interlace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid
namespace LamData
theorem _root_.solution {P : M.Par} {lam : ℕ → ℝ} {c g b : ℝ} (hL : LamData P lam c g b) {l : ℕ} (hl1 : 1 ≤ l)
    (hlk : l ≤ P.k) : PairData P l lam c g b where
  c_pos := hL.c_pos
  g_ge := hL.g_ge
  b_ge_three := hL.b_ge_three
  b_ge_k := hL.b_ge_k
  b_ge_c := hL.b_ge_c
  lam_le := hL.lam_le
  gap := hL.gap
  ul_le := hL.u_le l hl1 hlk
  pair := fun Y _ =>
    ⟨⟨0, pairOK_of_interlace P.k lam P.u 0 (-Y) fun s h1 h2 => (hL.inter s h1 h2).1⟩,
      ⟨0, pairOK_of_interlace P.k lam P.u' 0 (-Y) fun s h1 h2 => (hL.inter s h1 h2).2⟩⟩
end LamData
end CompanionTheory.WaveGrid
