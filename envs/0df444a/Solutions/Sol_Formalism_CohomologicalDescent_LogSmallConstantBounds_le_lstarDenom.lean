-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.le_lstarDenom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:35.67307+00:00
-- url     : https://prove2.me/submissions/b3c5dd5d-1135-4c3a-bed7-f7f63b03b265

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    (P.t : ℝ) ^ 3 * P.L ^ 2 ≤ lstarDenom P := by
  have nb := natBounds H
  have hS := H.S_nonneg
  have hL := G.L_ge
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hN : 0 ≤ P.N := by unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.N; positivity
  have h1 : (P.t : ℝ) ≤ P.n * (P.N + P.t) := by
    nlinarith [mul_nonneg (sub_nonneg.2 nb.n1) (add_nonneg hN ht0)]
  have h2 : 0 ≤ (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + P.t + P.L) :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ (P.t : ℝ) ^ 2 * P.L ^ 2 := by positivity
  have h3 : (P.t : ℝ) ^ 3 * P.L ^ 2 ≤ P.n * P.t ^ 2 * (P.N + P.t) * P.L ^ 2 := by
    calc (P.t : ℝ) ^ 3 * P.L ^ 2 = ((P.t : ℝ) ^ 2 * P.L ^ 2) * P.t := by ring
      _ ≤ ((P.t : ℝ) ^ 2 * P.L ^ 2) * (P.n * (P.N + P.t)) := mul_le_mul_of_nonneg_left h1 h4
      _ = P.n * P.t ^ 2 * (P.N + P.t) * P.L ^ 2 := by ring
  unfold lstarDenom
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
