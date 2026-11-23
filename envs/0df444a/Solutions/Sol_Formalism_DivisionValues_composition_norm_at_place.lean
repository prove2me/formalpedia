-- Prove2me | solution 1 for Formalism.DivisionValues.composition_norm_at_place
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:59.053892+00:00
-- url     : https://prove2.me/submissions/26c9ba22-2fa2-456c-92e7-22591effe755

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_prod_filter_succ
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_last
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_zero
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_nrm_mul_le
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_mulVecLin
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_mulVecLin_ne_zero
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_opNormAt_pos


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
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : CompNormAt := by
  intro K _ _ _ m c Xc hX Kj
  have key : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
      ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) := by
    intro v
    simp only [opNormAt_mulVecLin]
    have step : ∀ i : Fin (m + 1), nrm ((Xc i v)⁻¹ * (chainMat Kj i).map v.embedding * Xc 0 v) ≤
        ∏ j ∈ Finset.univ.filter (fun j : Fin m => j.castSucc < i),
          nrm ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v) := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [filter_zero, Finset.prod_empty]
        have h1 : chainMat Kj 0 = 1 := rfl
        rw [h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
          Matrix.nonsing_inv_mul _ (hX 0 v)]
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
        simp
      | succ j ih =>
        rw [prod_filter_succ]
        have h1 : chainMat Kj j.succ = Kj j * chainMat Kj j.castSucc := rfl
        have h2 : (Xc j.succ v)⁻¹ * (chainMat Kj j.succ).map v.embedding * Xc 0 v =
            ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v) *
              ((Xc j.castSucc v)⁻¹ * (chainMat Kj j.castSucc).map v.embedding * Xc 0 v) := by
          rw [h1, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (Xc j.castSucc v), Matrix.mul_nonsing_inv _ (hX _ v), Matrix.one_mul]
        rw [h2]
        exact (nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
    have := step (Fin.last m)
    rwa [filter_last] at this
  refine ⟨key, fun hne => ?_⟩
  have hpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos _ _ _ _ (hX _) (hX _) v _ (mulVecLin_ne_zero _ hne)
  have hterm : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ^ 2) ≤
      ∑ j : Fin m, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2) := by
    intro v
    have hprod := (hpos v).trans_le (key v)
    have hne' : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2 ≠ 0 := by
      intro j hj
      exact pow_ne_zero 2 (Finset.prod_ne_zero_iff.1 hprod.ne' j hj)
    rw [← Real.log_prod hne', Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)
  simp only [Formalism.HN.htMap]
  rw [← Finset.mul_sum, Finset.sum_comm]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hterm v) (by positivity)
end Formalism.DivisionValues
