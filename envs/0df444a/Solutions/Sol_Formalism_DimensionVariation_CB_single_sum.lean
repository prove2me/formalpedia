-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.single_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:47.604799+00:00
-- url     : https://prove2.me/submissions/d196f995-4349-4e8e-aaa2-0f08dd22fb2b

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
theorem _root_.solution {I X : Type} [DecidableEq I] {H : I → Type} [∀ i, AddCommMonoid (H i)] (i : I)
    (s : Finset X) (x : X → H i) :
    (Pi.single i (∑ a ∈ s, x a) : ∀ i, H i) = ∑ a ∈ s, Pi.single i (x a) :=
  map_sum (AddMonoidHom.single H i) x s
end Formalism.DimensionVariation.CB
