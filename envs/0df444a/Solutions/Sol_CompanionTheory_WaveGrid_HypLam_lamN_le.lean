-- Prove2me | solution 1 for CompanionTheory.WaveGrid.HypLam.lamN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:36:46.985679+00:00
-- url     : https://prove2.me/submissions/1efdb117-79a7-49ed-bcfe-f33082a7652d

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Theorems.Thm_CompanionTheory_WaveGrid_lamN_succ

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
namespace HypLam
theorem _root_.solution (h : HypLam P.k P.r lam c g b) :
    ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lamN lam s| ≤ b := by
  intro s hs1 hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [show lamN lam (t + 1) = lam ⟨t, by omega⟩ from lamN_succ lam ⟨t, by omega⟩]
  exact h.lam_le _
end HypLam
end CompanionTheory.WaveGrid
