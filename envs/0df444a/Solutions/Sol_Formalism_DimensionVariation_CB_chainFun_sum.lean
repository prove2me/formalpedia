-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.chainFun_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:17.967745+00:00
-- url     : https://prove2.me/submissions/c6ad8308-3841-45d9-b0a9-f5dbb33198c6

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
theorem _root_.solution {m : ℕ} {C : Fin (m + 1) → Type} [∀ i, AddCommMonoid (C i)]
    (Kj : ∀ j : Fin m, C j.castSucc →+ C j.succ) {X : Type} (s : Finset X) (x : X → C 0) (i : Fin (m + 1)) :
    chainFun (fun j => ⇑(Kj j)) i (∑ a ∈ s, x a) = ∑ a ∈ s, chainFun (fun j => ⇑(Kj j)) i (x a) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
    show Kj j (chainFun (fun j => ⇑(Kj j)) j.castSucc (∑ a ∈ s, x a)) =
      ∑ a ∈ s, Kj j (chainFun (fun j => ⇑(Kj j)) j.castSucc (x a))
    rw [ih, map_sum]
end Formalism.DimensionVariation.CB
