-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.size_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:47.35913+00:00
-- url     : https://prove2.me/submissions/1551f52c-8818-4ff9-81fa-fb04a17f3fc2

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_sizeOut_core
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_sizeSecond_core
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_band_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_cp_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_discriminant_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_floors_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_high_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_or_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_orders_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_prime_high_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_prime_low_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tDetD P m T ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P m T := by
  have a1 := size_floors_bound P e K m T hW hL hm hT
  have a2 := size_cp_bucket_bound P e K m T hW hL hm hT
  have a3 := size_prime_low_bound P e K m T hW hL hm hT
  have a4 := size_prime_high_bound P e K m T hW hL hm hT
  have a5 := size_or_bucket_bound P e K m T hW hL hm hT
  have a6 := sizeOut_core hW hL hm hT
  have a7 := size_orders_bucket_bound P e K m T hW hL hm hT
  have a8 := size_band_bound P e K m T hW hL hm hT
  have a9 := size_high_bucket_bound P e K m T hW hL hm hT
  have a10 := size_discriminant_bound P e K m T hW hL hm hT
  have a11 := sizeSecond_core hW hL hm hT
  unfold tDetD
  linarith
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
