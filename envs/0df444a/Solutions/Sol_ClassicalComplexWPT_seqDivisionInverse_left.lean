-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionInverse_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:12.217029+00:00
-- url     : https://prove2.me/submissions/e4fdf07a-8dec-48be-8d28-e4c225d42bc8

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
    (q : L1Coeff ℕ) :
    seqDivisionInverse d p hp (q + seqHighShift d (convolution q p)) = q := by
  let T := -(seqDivisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_seqDivisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff ℕ →L[ℂ] L1Coeff ℕ ↦ L q)
    (Units.inv_mul (Units.oneSub T hT))
  simpa [seqDivisionInverse, T, hT, seqDivisionPerturbation_apply,
    sub_eq_add_neg] using h
end ClassicalComplexWPT
