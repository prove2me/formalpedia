-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionInverse_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:06.811459+00:00
-- url     : https://prove2.me/submissions/a4daa234-2b08-443c-85f7-69a08f0542b3

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero


attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (b : L1Coeff ℕ) :
    seqDivisionInverse d p hp b +
      seqHighShift d (convolution (seqDivisionInverse d p hp b) p) = b := by
  let T := -(seqDivisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_seqDivisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff ℕ →L[ℂ] L1Coeff ℕ ↦ L b)
    (Units.mul_inv (Units.oneSub T hT))
  simpa [seqDivisionInverse, T, hT, seqDivisionPerturbation_apply,
    sub_eq_add_neg] using h
end ClassicalComplexWPT
