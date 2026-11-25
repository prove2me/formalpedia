-- Prove2me | solution 1 for CompanionTheory.WaveGrid.movedData_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:40.968304+00:00
-- url     : https://prove2.me/submissions/1f1e7183-b844-487f-9986-47ae960faef1

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
theorem _root_.solution (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) {l : ℕ} (hl1 : 1 ≤ l)
    (hlk : l ≤ P.k) (hmv : ∀ i, i ≠ l → P.u' i = P.u i) (hl : |P.u' l| ≤ b) : MovedData P l (lamN lam) c g b where
  c_pos := by linarith [h.c_ge]
  g_ge := by linarith [h.c_ge, h.g_ge]
  b_ge_three := h.b_ge_three
  b_ge_k := h.k_le
  b_ge_c := h.b_ge_c
  lam_le := h.lamN_le
  gap := h.lamN_gap
  inter := fun s h1 h2 => inter_half h.hc hu s h1 h2
  moved := hmv
  ul_le := ⟨hu.u_le l hl1 hlk, hl⟩
end CompanionTheory.WaveGrid
