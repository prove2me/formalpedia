-- Prove2me | solution 1 for ClassicalComplexWPT.evalL1PowerSeries_monomialSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:46.427855+00:00
-- url     : https://prove2.me/submissions/c7cdc98c-6b24-402a-a521-2f073ef8ff71

import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_tsum
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



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (monomialSeq d) w = w ^ d := by
  rw [evalL1PowerSeries_eq_tsum _ hw, tsum_eq_single d]
  · simp [monomialSeq_apply_same]
  · intro k hkd
    simp [monomialSeq_apply_ne hkd]
end ClassicalComplexWPT
