-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.two_gamma_le_three_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:34.320722+00:00
-- url     : https://prove2.me/submissions/e56c4a6a-a30b-4026-a605-56332be8e396

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) : 2 * gam l ≤ 3 / (l : ℝ) := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < l := by linarith
  have h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1 := by nlinarith
  rw [mul_div_assoc']
  first
  | (rw [div_le_div_iff₀ h2 h1]; nlinarith)
  | (rw [div_le_div_iff h2 h1]; nlinarith)
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
