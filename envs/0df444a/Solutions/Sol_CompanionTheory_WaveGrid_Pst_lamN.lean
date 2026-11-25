-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Pst_lamN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:38:35.247451+00:00
-- url     : https://prove2.me/submissions/dff7642a-fb64-4efb-9e7d-241205177fb4

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
namespace CompanionTheory.WaveGrid
theorem _root_.solution (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c y : ℝ) : Pst k r (lamN lam) c y = PStar lam c y := by
  unfold Pst PStar
  symm
  refine Finset.prod_bij (fun s _ => (s : ℕ) + 1) (fun s _ => ?_) (fun s _ t _ h => ?_) (fun t ht => ?_)
    (fun s _ => ?_)
  · have := s.2
    exact mem_Icc.2 ⟨by omega, by omega⟩
  · exact Fin.ext (by omega)
  · obtain ⟨h1, h2⟩ := mem_Icc.1 ht
    exact ⟨⟨t - 1, by omega⟩, mem_univ _, by simp only; omega⟩
  · rw [lamN_succ]
end CompanionTheory.WaveGrid
