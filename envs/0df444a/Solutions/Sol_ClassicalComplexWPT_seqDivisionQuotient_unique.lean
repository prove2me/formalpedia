-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionQuotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:00.632037+00:00
-- url     : https://prove2.me/submissions/6f19f3a4-f3f2-471e-83b4-e6e4aef8804c

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqDivisionInverse_left

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q r : L1Coeff ℕ)
    (hfac : f = seqLowShift d q + convolution q p + r)
    (hr : seqHighShift d r = 0) : q = seqDivisionQuotient d p hp f := by
  have hmap := congrArg (seqHighShiftCLM d) hfac
  have heq : q + seqHighShift d (convolution q p) = seqHighShift d f := by
    change seqHighShift d f = seqHighShift d (seqLowShift d q + convolution q p + r) at hmap
    rw [seqHighShift_add, seqHighShift_add, seqHighShift_seqLowShift, hr, add_zero] at hmap
    exact hmap.symm
  change q = seqDivisionInverse d p hp (seqHighShift d f)
  rw [← heq]
  exact (seqDivisionInverse_left d p hp q).symm
end ClassicalComplexWPT
