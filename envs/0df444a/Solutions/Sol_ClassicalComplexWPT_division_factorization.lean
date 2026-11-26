-- Prove2me | solution 1 for ClassicalComplexWPT.division_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:18.844548+00:00
-- url     : https://prove2.me/submissions/6ad867a5-d4fb-4528-8d9e-16422f2481aa

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_lowShift_highShift_add_lowCut
import Theorems.Thm_ClassicalComplexWPT_divisionQuotient_equation

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) :
    f = lowShift d (divisionQuotient d p hp f) +
      convolution (divisionQuotient d p hp f) p + divisionRemainder d p hp f := by
  let q := divisionQuotient d p hp f
  have hq := divisionQuotient_equation d p hp f
  have hhigh : highShift d (f - convolution q p) = q := by
    change highShiftCLM d (f - convolution q p) = q
    rw [map_sub]
    change highShift d f - highShift d (convolution q p) = q
    rw [← hq]
    abel
  have hdec := lowShift_highShift_add_lowCut d (f - convolution q p)
  rw [hhigh] at hdec
  change f = lowShift d q + convolution q p + lowCut d (f - convolution q p)
  calc
    f = (f - convolution q p) + convolution q p := by abel
    _ = (lowShift d q + lowCut d (f - convolution q p)) + convolution q p :=
      congrArg (fun x ↦ x + convolution q p) hdec.symm
    _ = lowShift d q + convolution q p + lowCut d (f - convolution q p) := by abel
end ClassicalComplexWPT
