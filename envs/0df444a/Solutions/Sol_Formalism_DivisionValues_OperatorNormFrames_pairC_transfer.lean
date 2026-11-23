-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.pairC_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:38.742606+00:00
-- url     : https://prove2.me/submissions/d0b9856c-91ac-41e3-9070-d995d550d7fe

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_pairC_eq
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_dual_expand
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_map_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {K : Type} [Field K] [NumberField K] {a b n D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (A : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (N : Matrix (Fin D) (Fin n) K) (C : Matrix (Fin b) (Fin a) K)
    (h : ∀ φ F, B φ (N.mulVec F) = A (C.mulVec φ) F) (x : Fin a → ℂ) (F : Fin n → ℂ) :
    pairC v B x ((N.map v.embedding).mulVec F) = pairC v A ((C.map v.embedding).mulVec x) F := by
  have key : ∀ i l, ∑ k, N k l * B (Pi.single i 1) (Pi.single k 1) =
      ∑ j, C j i * A (Pi.single j 1) (Pi.single l 1) := by
    intro i l
    have h1 := h (Pi.single i 1) (Pi.single l 1)
    rw [dual_expand (B (Pi.single i 1)), map_expand A] at h1
    simpa [Matrix.mulVec_single_one] using h1
  have hM : (N.map v.embedding)ᵀ * pmat v B = pmat v A * C.map v.embedding := by
    ext l i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, pmat, Matrix.of_apply]
    have := congrArg v.embedding (key i l)
    simp only [map_sum, map_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [pairC_eq, pairC_eq, Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
end Formalism.DivisionValues.OperatorNormFrames
