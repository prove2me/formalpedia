-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.extra_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:19:33.091064+00:00
-- url     : https://prove2.me/submissions/c030fe21-63ce-4979-b15c-ddd6d01724f1

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
open Formalism.DimensionVariation.CB
namespace Formalism.DimensionVariation.CB
theorem _root_.solution (a b f m N L La logg C8 : ℝ) (ha : a ≤ f * N ^ 2 * logg) (hb : b ≤ f * N ^ 2 * logg)
    (hf : 0 ≤ f) (hm : 1 ≤ m) (hL : 0 ≤ L) (hLLa : L ≤ La) (hg : logg ≤ C8 * L) (p8 : 0 ≤ C8) :
    a + b ≤ 2 * C8 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by
  have hN : 0 ≤ f * N ^ 2 := mul_nonneg hf (sq_nonneg N)
  have h1 : f * N ^ 2 * logg ≤ f * N ^ 2 * (C8 * La) :=
    mul_le_mul_of_nonneg_left (le_trans hg (mul_le_mul_of_nonneg_left hLLa p8)) hN
  have hm3 : 0 ≤ m ^ 3 := pow_nonneg (le_trans zero_le_one hm) 3
  have h2 : 0 ≤ C8 * (f * m ^ 3 * N ^ 2 * L) :=
    mul_nonneg p8 (mul_nonneg (mul_nonneg (mul_nonneg hf hm3) (sq_nonneg N)) hL)
  nlinarith [h1, h2, ha, hb]
end Formalism.DimensionVariation.CB
