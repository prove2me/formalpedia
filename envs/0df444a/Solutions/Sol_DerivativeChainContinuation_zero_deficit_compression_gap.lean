-- Prove2me | solution 1 for DerivativeChainContinuation.zero_deficit_compression_gap
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:34:37.093026+00:00
-- url     : https://prove2.me/submissions/3ed1948e-c76a-4e4b-9616-3b02de7245e5

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AllScaleCompression
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_all_scale_arbitrary_source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℂ)
    (hzero : schoenbergDeficit (∏ i,(X-C (a i-complexCentroid a)))=0)
    (z : ℂ) (t : ℝ) (ht : 0 < t) : scaleCompressionGap (fun i => a i-z) t=0 := by
  have h := all_scale_arbitrary_source n hn a z t ht
  have hu : scaleCompressionGap (fun i => a i-z) t ≤ 0 := by simpa only [hzero,zero_div,min_eq_right zero_le_one,mul_zero] using h.2.1
  exact le_antisymm hu h.1
