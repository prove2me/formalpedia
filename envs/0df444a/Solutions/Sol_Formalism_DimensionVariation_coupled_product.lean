-- Prove2me | solution 1 for Formalism.DimensionVariation.coupled_product
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.444472+00:00
-- url     : https://prove2.me/submissions/369a8f50-207f-4d6d-b98b-c97632408541

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
namespace Formalism.DimensionVariation
theorem _root_.solution : CoupledProduct := by
  intro AA Rep Y Cl2 _ Cl _ _ _ A B C _ _ _ _ _ _ γ0 γ1 ε1 T1 ε2 T2 G g'
  simp only [liftOp, coupledOp, map_sum, map_smul, Finset.smul_sum, smul_smul, Fintype.sum_sigma,
    mul_assoc]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
end Formalism.DimensionVariation
