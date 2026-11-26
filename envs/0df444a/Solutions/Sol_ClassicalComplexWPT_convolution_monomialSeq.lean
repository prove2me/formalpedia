-- Prove2me | solution 1 for ClassicalComplexWPT.convolution_monomialSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:25.30033+00:00
-- url     : https://prove2.me/submissions/f6596ed0-3d86-4cff-95cc-7f69a4c2eafc

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
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
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_apply_of_le
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_apply_of_lt
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



set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (q : OriginSeq) (d : ℕ) :
    convolution q (monomialSeq d) = seqLowShift d q := by
  apply lp.ext
  funext n
  rw [convolution_apply]
  by_cases hn : n < d
  · rw [seqLowShift_apply_of_lt d q hn]
    apply Finset.sum_eq_zero
    intro ij hij
    have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hne : ij.2 ≠ d := by omega
    rw [monomialSeq_apply_ne hne, mul_zero]
  · have hdn : d ≤ n := Nat.le_of_not_gt hn
    rw [seqLowShift_apply_of_le d q hdn]
    rw [Finset.sum_eq_single (n - d, d)]
    · rw [monomialSeq_apply_same, mul_one]
    · intro ij hij hne
      have hdne : ij.2 ≠ d := by
        intro heq
        apply hne
        have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        apply Prod.ext
        · simp only
          omega
        · simpa only [Prod.snd] using heq
      rw [monomialSeq_apply_ne hdne, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_antidiagonal]
      omega
end ClassicalComplexWPT
