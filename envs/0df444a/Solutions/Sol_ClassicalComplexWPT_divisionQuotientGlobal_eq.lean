-- Prove2me | solution 1 for ClassicalComplexWPT.divisionQuotientGlobal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:59.098843+00:00
-- url     : https://prove2.me/submissions/3c4d462b-749b-4eef-b32e-1612e56a6c5e

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p f : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1) :
    divisionQuotientGlobal d (p,f) = divisionQuotient d p hp f := by
  let K := divisionPerturbation d p
  let hK : ‖-K‖ < 1 := norm_neg_divisionPerturbation_lt_one d p hp
  have hinv : Ring.inverse (1 + K) = ↑((Units.oneSub (-K) hK)⁻¹) := by
    rw [show 1 + K = 1 - (-K) by abel]
    exact NormedRing.inverse_one_sub (-K) hK
  change Ring.inverse (1 + K) (highShift d f) =
    (↑((Units.oneSub (-K) hK)⁻¹) :
      L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ)) (highShift d f)
  rw [hinv]
end ClassicalComplexWPT
