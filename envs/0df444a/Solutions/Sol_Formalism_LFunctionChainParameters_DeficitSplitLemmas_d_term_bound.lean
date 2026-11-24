-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.d_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:39.668278+00:00
-- url     : https://prove2.me/submissions/25cd7f68-c1d1-4b50-a739-69302a067837

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_askAt_le_geom
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_geom_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution : DTerm := by
  intro I a at_ d w hd ha hat hw hI
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have h1 := askAt_le_geom I at_ d w hd0 ha hw
  have hq : 1 / (d : ℝ) < 1 := by
    rw [div_lt_one hd0]; linarith
  have h2 := geom_pos I (1 / (d : ℝ)) (by positivity) hq hI
  have e1 : 1 / (d : ℝ) / (1 - 1 / (d : ℝ)) = 1 / ((d : ℝ) - 1) := by
    have : (d : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [e1] at h2
  have h3 : at_ * (1 / ((d : ℝ) - 1)) ≤ 2 * a / d := by
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    rw [mul_one_div, div_le_div_iff₀ hd1 hd0]
    have ha' : 0 ≤ a := by linarith
    nlinarith
  have h4 := (h1.trans (mul_le_mul_of_nonneg_left h2 ha)).trans h3
  have hl : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have h5 := mul_le_mul_of_nonneg_left h4 hl
  have e : Real.log d * (2 * a / d) = 2 * a * Real.log d / d := by ring
  rw [e] at h5
  exact h5
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
