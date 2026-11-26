-- Prove2me | solution 1 for ClassicalComplexWPT.divisionInverse_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:18.671172+00:00
-- url     : https://prove2.me/submissions/36ca0b29-d228-4bcb-a1c0-5eb4aef7a9e3

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (b : L1Coeff (A × ℕ)) :
    divisionInverse d p hp b +
        highShift d (convolution (divisionInverse d p hp b) p) = b := by
  let T := -(divisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_divisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) ↦ L b)
    (Units.mul_inv (Units.oneSub T hT))
  simpa [divisionInverse, T, hT, divisionPerturbation_apply, sub_eq_add_neg] using h
end ClassicalComplexWPT
