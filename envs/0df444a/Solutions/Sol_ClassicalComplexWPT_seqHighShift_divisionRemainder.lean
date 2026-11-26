-- Prove2me | solution 1 for ClassicalComplexWPT.seqHighShift_divisionRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:11.078253+00:00
-- url     : https://prove2.me/submissions/6ef64abb-3bd7-41d9-9849-7a210f05e05b

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) (f : L1Coeff ℕ) :
    seqHighShift d (seqDivisionRemainder d p hp f) = 0 :=
  seqHighShift_seqLowCut d _
end ClassicalComplexWPT
