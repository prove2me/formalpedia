-- Prove2me | solution 1 for ClassicalComplexWPT.seqPreparedPolynomial_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:47.262113+00:00
-- url     : https://prove2.me/submissions/43621a3a-4f50-4136-ad1d-816c76493fbb

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Theorems.Thm_ClassicalComplexWPT_constantOneSeq_apply
import Theorems.Thm_ClassicalComplexWPT_convolution_constantOneSeq
import Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_apply_fin
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_preparedTailSeq
import Theorems.Thm_ClassicalComplexWPT_seqDivision_zero_remainder_unique
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainderGlobal
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.constantOneSeq_apply
attribute [local simp] ClassicalComplexWPT.convolution_constantOneSeq
attribute [local simp] ClassicalComplexWPT.preparedTailSeq_apply_fin
attribute [local simp] ClassicalComplexWPT.seqHighShift_preparedTailSeq

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p p' v : L1Coeff ℕ)
    (hp' : ‖p'‖ < 1)
    (hpLow : seqHighShift d p = 0)
    (hp'Low : seqHighShift d p' = 0)
    (hfactor :
      seqLowShift d constantOneSeq + p =
        seqLowShift d v + convolution v p') :
    p = p' ∧ v = constantOneSeq := by
  let f := seqLowShift d constantOneSeq + p
  have hfacRatio : f = seqLowShift d v + convolution v p' := hfactor
  have hfacOne : f =
      seqLowShift d constantOneSeq + convolution constantOneSeq p' + (p - p') := by
    dsimp only [f]
    rw [convolution_constantOneSeq]
    abel
  have hremLow : seqHighShift d (p - p') = 0 := by
    change seqHighShiftCLM d (p - p') = 0
    rw [map_sub]
    change seqHighShift d p - seqHighShift d p' = 0
    rw [hpLow, hp'Low, sub_self]
  have huniq := seqDivision_zero_remainder_unique d p' hp' f v constantOneSeq
    (p - p') hfacRatio hfacOne hremLow
  refine ⟨?_, huniq.1⟩
  exact sub_eq_zero.mp huniq.2
end ClassicalComplexWPT
