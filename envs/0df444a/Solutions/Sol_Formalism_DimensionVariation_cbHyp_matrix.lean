-- Prove2me | solution 1 for Formalism.DimensionVariation.cbHyp_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:21.90769+00:00
-- url     : https://prove2.me/submissions/d77821c1-da20-47b7-be61-5d81569d41ce

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
theorem _root_.solution (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (tmax : Fin m → InfinitePlace K → ℝ) (h0 : ∀ j v, 0 ≤ tmax j v)
    (ht : ∀ j v q p, ‖v.embedding (Kj j q p)‖ ^ 2 ≤ tmax j v) :
    CBHyp (fun i _ => (1 : Matrix (Fin (c i)) (Fin (c i)) ℂ)) Kj (AA := fun i => Fin (c i))
      (fun _ _ => Unit) (fun _ _ => ℂ) (fun _ _ => 1) (fun _ _ x p => x p.1) (fun _ _ _ _ => 1)
      (fun j v p q => (v.embedding (Kj j q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ) (fun _ => 1) tmax := by
  unfold CBHyp
  refine ⟨fun i v => by simp, fun i p => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_, h0,
    fun _ _ => by simp⟩
  · intro i v x
    simp only [Formalism.DivisionValues.fnorm, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Fintype.sum_sigma]
    simp
  · intro j v x
    funext q
    simp [liftOp, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  · intro j v p q
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact ht j v q.1 p.1
end Formalism.DimensionVariation
