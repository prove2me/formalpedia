-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionRemainderGlobal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:03:10.477865+00:00
-- url     : https://prove2.me/submissions/a5622f1b-1960-4dfe-9425-2d08429b96d3

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotientGlobal_eq
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero


attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    seqDivisionRemainderGlobal d (p,f) = seqDivisionRemainder d p hp f := by
  simp only [seqDivisionRemainderGlobal, seqDivisionRemainder]
  rw [seqDivisionQuotientGlobal_eq d p f hp]
end ClassicalComplexWPT
