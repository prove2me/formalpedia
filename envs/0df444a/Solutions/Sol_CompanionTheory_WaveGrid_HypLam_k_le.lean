-- Prove2me | solution 1 for CompanionTheory.WaveGrid.HypLam.k_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:01:15.556966+00:00
-- url     : https://prove2.me/submissions/cc4c2104-f994-4ab6-a057-dcac7858ccad

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie

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
theorem _root_.solution (h : HypLam P.k P.r lam c g b) : (P.k : ℝ) ≤ b := by
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have h2 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  nlinarith [h.b_ge_k]
end HypLam
end CompanionTheory.WaveGrid
