-- Prove2me | solution 1 for FirstPassageLinearTransport.weightedSurvivalFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:02.113877+00:00
-- url     : https://prove2.me/submissions/5d6a7261-d37d-4a2f-a61d-a9501ed98471

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_wordSurvivalIndicator_nonneg

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo z : ℝ) {r : ℕ} (v : Fin r → Bool) :
    0 ≤ weightedSurvivalFactor p x lo z v :=
  mul_nonneg (bernoulliWordWeight_nonneg hp₀ hp₁ v)
    (wordSurvivalIndicator_nonneg lo x z v)
end FirstPassageLinearTransport
