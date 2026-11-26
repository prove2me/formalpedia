-- Prove2me | solution 1 for ClassicalComplexWPT.weighted_scaled_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:39.214509+00:00
-- url     : https://prove2.me/submissions/adc4a141-2089-4306-8e87-b6974eb96001

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (r : ℂ) (hr : r ≠ 0) {d i : ℕ} (hi : i ≤ d)
    (w : ℂ) :
    r ^ (d - i) * w ^ i = r ^ d * (r⁻¹ * w) ^ i := by
  rw [pow_sub₀ r hr hi, mul_pow, inv_pow]
  ring
end ClassicalComplexWPT
