-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.nrm_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:46.968212+00:00
-- url     : https://prove2.me/submissions/e5d24155-ddba-4dd2-8722-28db3fc1692b

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
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DimensionVariation.CB
theorem _root_.solution {a b : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) (X' : Matrix (Fin b) (Fin b) ℂ)
    (hX : IsUnit X.det) (M : Matrix (Fin b) (Fin a) ℂ) (Bd : ℝ) (hB : 0 ≤ Bd)
    (h : ∀ y, fnorm X' (M.mulVec y) ^ 2 ≤ Bd * fnorm X y ^ 2) :
    nrm (X'⁻¹ * M * X) ≤ Real.sqrt Bd := by
  unfold nrm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun z => ?_)
  have key : ∀ (A' : Matrix (Fin b) (Fin a) ℂ),
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A')) z‖ =
        Formalism.HermitianLatticesTheory.cnorm (A'.mulVec (fun i => z i)) := by
    intro A'
    rw [EuclideanSpace.norm_eq]
    rfl
  have hz : ‖z‖ = Formalism.HermitianLatticesTheory.cnorm (fun i => z i) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [key, hz]
  have e1 : (X'⁻¹ * M * X).mulVec (fun i => z i) = X'⁻¹.mulVec (M.mulVec (X.mulVec (fun i => z i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have e2 : X⁻¹.mulVec (X.mulVec (fun i => z i)) = (fun i => z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul X hX, Matrix.one_mulVec]
  have hy := h (X.mulVec (fun i => z i))
  unfold Formalism.DivisionValues.fnorm at hy
  rw [e2, ← e1] at hy
  have c0 : 0 ≤ Formalism.HermitianLatticesTheory.cnorm ((X'⁻¹ * M * X).mulVec (fun i => z i)) := Real.sqrt_nonneg _
  have c1 : 0 ≤ Formalism.HermitianLatticesTheory.cnorm (fun i => z i) := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq c0, ← Real.sqrt_sq c1, ← Real.sqrt_mul hB]
  exact Real.sqrt_le_sqrt hy
end Formalism.DimensionVariation.CB
