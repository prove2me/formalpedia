-- Prove2me | solution 1 for ClassicalComplexWPT.divisionQuotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:57.545798+00:00
-- url     : https://prove2.me/submissions/bac42fc4-c9c6-4a4a-922b-4a8948b9a61c

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_divisionInverse_left

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f q r : L1Coeff (A × ℕ))
    (hfac : f = lowShift d q + convolution q p + r)
    (hr : highShift d r = 0) : q = divisionQuotient d p hp f := by
  have hmap := congrArg (highShiftCLM (A := A) d) hfac
  have heq : q + highShift d (convolution q p) = highShift d f := by
    change highShift d f = highShift d (lowShift d q + convolution q p + r) at hmap
    rw [highShift_add, highShift_add, highShift_lowShift, hr, add_zero] at hmap
    exact hmap.symm
  change q = divisionInverse d p hp (highShift d f)
  rw [← heq]
  exact (divisionInverse_left d p hp q).symm
end ClassicalComplexWPT
