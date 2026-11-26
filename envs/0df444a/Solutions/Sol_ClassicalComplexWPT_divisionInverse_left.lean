-- Prove2me | solution 1 for ClassicalComplexWPT.divisionInverse_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:19.369352+00:00
-- url     : https://prove2.me/submissions/c3ac5e7a-6aa4-4ec0-8405-bcdd315807c2

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
    (q : L1Coeff (A × ℕ)) :
    divisionInverse d p hp (q + highShift d (convolution q p)) = q := by
  let T := -(divisionPerturbation d p)
  let hT : ‖T‖ < 1 := norm_neg_divisionPerturbation_lt_one d p hp
  have h := congrArg (fun L : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) ↦ L q)
    (Units.inv_mul (Units.oneSub T hT))
  simpa [divisionInverse, T, hT, divisionPerturbation_apply, sub_eq_add_neg] using h
end ClassicalComplexWPT
