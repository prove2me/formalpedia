-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.inv_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:37.420443+00:00
-- url     : https://prove2.me/submissions/09d39070-2b78-4797-bef5-56f9750e8e09

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
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) : 1 / (l : ℝ) ≤ gam l := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < l := by linarith
  have h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1 := by nlinarith
  first
  | (rw [div_le_div_iff₀ h1 h2]; nlinarith)
  | (rw [div_le_div_iff h1 h2]; nlinarith)
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
