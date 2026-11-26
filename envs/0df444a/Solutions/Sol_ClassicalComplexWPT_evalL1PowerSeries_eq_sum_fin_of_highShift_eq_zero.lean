-- Prove2me | solution 1 for ClassicalComplexWPT.evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:46.945607+00:00
-- url     : https://prove2.me/submissions/cc95a196-233b-4486-be6d-b19bc0f2f21e

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
theorem _root_.solution
    (d : ℕ) (a : L1Sequence) (ha : seqHighShift d a = 0)
    {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries a w = ∑ i : Fin d, a i * w ^ (i : ℕ) := by
  rw [evalL1PowerSeries_eq_tsum _ hw]
  let F : ℕ → ℂ := fun k ↦ a k * w ^ k
  change (∑' k : ℕ, F k) = ∑ i : Fin d, F i
  rw [Fin.sum_univ_eq_sum_range F d]
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have hcoord := congrArg (fun b : L1Sequence ↦ b (k - d)) ha
  change a ((k - d) + d) = 0 at hcoord
  rw [Nat.sub_add_cancel hk] at hcoord
  dsimp only [F]
  rw [hcoord, zero_mul]
end ClassicalComplexWPT
