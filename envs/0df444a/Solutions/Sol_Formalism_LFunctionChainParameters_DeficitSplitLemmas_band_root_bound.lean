-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.band_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:22.372117+00:00
-- url     : https://prove2.me/submissions/c65611b2-04b8-41d0-8821-91504e8dca28

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
theorem _root_.solution : BandRoot := by
  intro X' ρ p i hX hρ0 hρ1 hp hi hlo hhi
  have hi0 : i ≠ 0 := by omega
  set R : ℝ := X' ^ ((1 : ℝ) / i) with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hX _
  have hRi : R ^ i = X' := by
    rw [hR, one_div]; exact Real.rpow_inv_natCast_pow hX.le hi0
  constructor
  · by_contra hcon
    have hlt : p < R * (1 - ρ) := not_le.1 hcon
    have h1 : p ^ i < (R * (1 - ρ)) ^ i := pow_lt_pow_left₀ hlt hp hi0
    rw [mul_pow, hRi] at h1
    have h2 : (1 - ρ) ^ i ≤ 1 - ρ := pow_le_of_le_one (by linarith) (by linarith) hi0
    have h3 : X' * (1 - ρ) ^ i ≤ X' * (1 - ρ) := mul_le_mul_of_nonneg_left h2 hX.le
    linarith
  · by_contra hcon
    have hlt : R * (1 + ρ) < p := not_le.1 hcon
    have h1 : (R * (1 + ρ)) ^ i < p ^ i := pow_lt_pow_left₀ hlt (by positivity) hi0
    rw [mul_pow, hRi] at h1
    have h2 : 1 + ρ ≤ (1 + ρ) ^ i := le_self_pow₀ (by linarith) hi0
    have h3 : X' * (1 + ρ) ≤ X' * (1 + ρ) ^ i := mul_le_mul_of_nonneg_left h2 hX.le
    linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
