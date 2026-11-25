-- Prove2me | solution 1 for CompanionTheory.WaveGrid.HypLam.lamN_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:38:16.343929+00:00
-- url     : https://prove2.me/submissions/692e58a3-870a-4786-97b3-6cc9cfdb697e

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
    ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lamN lam (s + 1) + g ≤ lamN lam s := by
  intro s hs1 hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [show lamN lam (t + 1) = lam ⟨t, by omega⟩ from lamN_succ lam ⟨t, by omega⟩,
    show lamN lam (t + 1 + 1) = lam ⟨t + 1, by omega⟩ from lamN_succ lam ⟨t + 1, by omega⟩]
  exact h.gap _ _ rfl
end HypLam
end CompanionTheory.WaveGrid
