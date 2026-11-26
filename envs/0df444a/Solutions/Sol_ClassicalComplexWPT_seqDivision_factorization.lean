-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivision_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:49.012595+00:00
-- url     : https://prove2.me/submissions/2632d7ee-63df-4a6a-b7f0-6fd40089592d

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_highShift_add_lowCut
import Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotient_equation

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) :
    f = seqLowShift d (seqDivisionQuotient d p hp f) +
      convolution (seqDivisionQuotient d p hp f) p + seqDivisionRemainder d p hp f := by
  let q := seqDivisionQuotient d p hp f
  have hq := seqDivisionQuotient_equation d p hp f
  have hhigh : seqHighShift d (f - convolution q p) = q := by
    change seqHighShiftCLM d (f - convolution q p) = q
    rw [map_sub]
    change seqHighShift d f - seqHighShift d (convolution q p) = q
    rw [← hq]
    abel
  have hdec := seqLowShift_highShift_add_lowCut d (f - convolution q p)
  rw [hhigh] at hdec
  change f = seqLowShift d q + convolution q p + seqLowCut d (f - convolution q p)
  calc
    f = (f - convolution q p) + convolution q p := by abel
    _ = (seqLowShift d q + seqLowCut d (f - convolution q p)) + convolution q p :=
      congrArg (fun x ↦ x + convolution q p) hdec.symm
    _ = seqLowShift d q + convolution q p + seqLowCut d (f - convolution q p) := by abel
end ClassicalComplexWPT
