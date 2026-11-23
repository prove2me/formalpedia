-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.pos_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:47.156909+00:00
-- url     : https://prove2.me/submissions/2fe312ce-181b-4e33-bfc3-28e7dc3ce309

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
open Formalism.DimensionVariation.CB
namespace Formalism.DimensionVariation.CB
theorem _root_.solution {a b : ℝ} (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a ∧ 0 < b := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h' | h'
  · exact h'
  · exact absurd hb (not_le.mpr h'.2)
end Formalism.DimensionVariation.CB
