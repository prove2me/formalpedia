-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.card_sigma_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:45.374149+00:00
-- url     : https://prove2.me/submissions/5036e853-72d1-4649-8ad9-b04b6d2d9964

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
theorem _root_.solution {AA : Type} [Fintype AA] (Cl : AA → Type) [∀ a, Fintype (Cl a)] (h : ℝ)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) :
    (Fintype.card (Σ a, Cl a) : ℝ) ≤ (Fintype.card AA : ℝ) * h := by
  rw [Fintype.card_sigma]
  push_cast
  calc (∑ a, (Fintype.card (Cl a) : ℝ)) ≤ ∑ _a : AA, h := Finset.sum_le_sum (fun a _ => hh a)
    _ = (Fintype.card AA : ℝ) * h := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end Formalism.DimensionVariation.CB
