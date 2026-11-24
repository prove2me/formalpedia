-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.band_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:21.30281+00:00
-- url     : https://prove2.me/submissions/93602d5a-7f6c-4207-9555-ea3d19fa34f5

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma

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
theorem _root_.solution : BandExponent := by
  intro X' ρ p i hX hρ hp hpi
  have hp8 : (8 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow0 : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  have h1 : Real.log ((p : ℝ) ^ i) ≤ Real.log (2 * X') :=
    Real.log_le_log hpow0 (by nlinarith)
  rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h1
  have h2 : Real.log 2 ≤ Real.log X' := Real.log_le_log (by norm_num) hX
  have h8 : Real.log 8 ≤ Real.log p := Real.log_le_log (by norm_num) hp8
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hlp : 2 ≤ Real.log p := by linarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
