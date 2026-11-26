-- Prove2me | solution 1 for ClassicalComplexWPT.divisionRemainder_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:53.095195+00:00
-- url     : https://prove2.me/submissions/7297d0c9-c69d-406c-a0da-c0383f589d74

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
theorem _root_.solution (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ} (hn : d ≤ n) :
    divisionRemainder d p hp f (a,n) = 0 := by
  exact lowCut_apply_of_le d _ a hn
end ClassicalComplexWPT
