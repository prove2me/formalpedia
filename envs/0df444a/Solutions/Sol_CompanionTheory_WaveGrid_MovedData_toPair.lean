-- Prove2me | solution 1 for CompanionTheory.WaveGrid.MovedData.toPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:43.825817+00:00
-- url     : https://prove2.me/submissions/00b0e097-b778-457a-9d13-0b530dd8c3c6

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Theorems.Thm_CompanionTheory_WaveGrid_pairOK_of_moved
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
namespace MovedData
theorem _root_.solution {P : M.Par} {l : ℕ} {lam : ℕ → ℝ} {c g b : ℝ} (hM : MovedData P l lam c g b) :
    PairData P l lam c g b where
  c_pos := hM.c_pos
  g_ge := hM.g_ge
  b_ge_three := hM.b_ge_three
  b_ge_k := hM.b_ge_k
  b_ge_c := hM.b_ge_c
  lam_le := hM.lam_le
  gap := hM.gap
  ul_le := hM.ul_le
  pair := fun Y hY =>
    ⟨⟨0, pairOK_of_interlace P.k lam P.u 0 (-Y) hM.inter⟩,
      pairOK_of_moved P.k l lam P.u P.u' (-Y) hM.inter hM.moved (by
        rcases hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by linarith, by linarith⟩
        · exact Or.inr ⟨by linarith, by linarith⟩)⟩
end MovedData
end CompanionTheory.WaveGrid
