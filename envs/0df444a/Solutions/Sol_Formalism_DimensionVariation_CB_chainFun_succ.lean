-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.chainFun_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:46.000649+00:00
-- url     : https://prove2.me/submissions/7529458e-0f92-48a5-ab45-8bd734d3de0f

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
theorem _root_.solution {m : ℕ} {C : Fin (m + 2) → Type} (Kj : ∀ j : Fin (m + 1), C j.castSucc → C j.succ)
    (φ : C 0) (i : Fin (m + 1)) :
    chainFun Kj i.succ φ = chainFun (C := fun i => C i.succ) (fun j : Fin m => Kj j.succ) i (Kj 0 φ) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => exact congrArg (Kj j.succ) ih
end Formalism.DimensionVariation.CB
