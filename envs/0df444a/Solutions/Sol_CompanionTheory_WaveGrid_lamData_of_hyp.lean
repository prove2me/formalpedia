-- Prove2me | solution 1 for CompanionTheory.WaveGrid.lamData_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:49:21.196095+00:00
-- url     : https://prove2.me/submissions/98bbf67e-4bd4-4f19-8b49-8cf4e437f595

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Theorems.Thm_CompanionTheory_WaveGrid_inter_half
import Theorems.Thm_CompanionTheory_WaveGrid_HypLam_k_le
import Theorems.Thm_CompanionTheory_WaveGrid_HypLam_lamN_le
import Theorems.Thm_CompanionTheory_WaveGrid_HypLam_lamN_gap

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
variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ}
namespace CompanionTheory.WaveGrid
theorem _root_.solution (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hu' : HypType P.k P.r lam P.u' b) : LamData P (lamN lam) c g b where
  c_pos := by linarith [h.c_ge]
  g_ge := by linarith [h.c_ge, h.g_ge]
  b_ge_three := h.b_ge_three
  b_ge_k := h.k_le
  b_ge_c := h.b_ge_c
  lam_le := h.lamN_le
  gap := h.lamN_gap
  inter := fun s h1 h2 => ⟨inter_half h.hc hu s h1 h2, inter_half h.hc hu' s h1 h2⟩
  u_le := fun i h1 h2 => ⟨hu.u_le i h1 h2, hu'.u_le i h1 h2⟩
end CompanionTheory.WaveGrid
