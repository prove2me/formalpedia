-- Prove2me | solution 1 for ClassicalComplexWPT.divisionQuotient_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:56.834637+00:00
-- url     : https://prove2.me/submissions/473e6908-4fa7-4adf-bed8-23128a22bdba

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_divisionInverse_right

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) :
    divisionQuotient d p hp f +
        highShift d (convolution (divisionQuotient d p hp f) p) = highShift d f := by
  exact divisionInverse_right d p hp (highShift d f)
end ClassicalComplexWPT
