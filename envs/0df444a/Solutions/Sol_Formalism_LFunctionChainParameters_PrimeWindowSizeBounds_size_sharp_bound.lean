-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_sharp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:45.528137+00:00
-- url     : https://prove2.me/submissions/cc5bc9e1-374e-4722-934a-af548e335a52

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_floors_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_cp_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_prime_low_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_prime_high_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_or_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_bad_orbits_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_orders_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_band_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_high_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_discriminant_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_second_io_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : WindowSizeBoundSharp := by
  intro P e K m T hW hL hm hT
  have a1 := size_floors_bound P e K m T hW hL hm hT
  have a2 := size_cp_bucket_bound P e K m T hW hL hm hT
  have a3 := size_prime_low_bound P e K m T hW hL hm hT
  have a4 := size_prime_high_bound P e K m T hW hL hm hT
  have a5 := size_or_bucket_bound P e K m T hW hL hm hT
  have a6 := size_bad_orbits_bound P e K m T hW hL hm hT
  have a7 := size_orders_bucket_bound P e K m T hW hL hm hT
  have a8 := size_band_bound P e K m T hW hL hm hT
  have a9 := size_high_bucket_bound P e K m T hW hL hm hT
  have a10 := size_discriminant_bound P e K m T hW hL hm hT
  have a11 := size_second_io_bound P e K m T hW hL hm hT
  unfold tDet
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
