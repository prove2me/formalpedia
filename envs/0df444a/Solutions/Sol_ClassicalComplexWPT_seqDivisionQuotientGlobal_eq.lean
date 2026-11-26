-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionQuotientGlobal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:34.2798+00:00
-- url     : https://prove2.me/submissions/27810c80-1e63-4a4d-bef2-777309ea7518

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
theorem _root_.solution (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    seqDivisionQuotientGlobal d (p,f) = seqDivisionQuotient d p hp f := by
  let K := seqDivisionPerturbation d p
  let hK : ‖-K‖ < 1 := norm_neg_seqDivisionPerturbation_lt_one d p hp
  have hinv : Ring.inverse (1 + K) = ↑((Units.oneSub (-K) hK)⁻¹) := by
    rw [show 1 + K = 1 - (-K) by abel]
    exact NormedRing.inverse_one_sub (-K) hK
  change Ring.inverse (1 + K) (seqHighShift d f) =
    (↑((Units.oneSub (-K) hK)⁻¹) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ) (seqHighShift d f)
  rw [hinv]
end ClassicalComplexWPT
