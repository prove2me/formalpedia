-- Prove2me | solution 1 for ClassicalComplexWPT.preparationUnit_zero_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:10.165668+00:00
-- url     : https://prove2.me/submissions/43257cc9-b44a-4c9c-a6b5-ec54ddc70e88

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Theorems.Thm_ClassicalComplexWPT_preparationQuotientEval_zero

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hr0 : 0 < r) (htop : originWeightedCoeffs p r hr d ≠ 0)
    (hq0 : normalizedPreparationQuotient p r hr d 0 0 = 1) :
    preparationUnit p r hr d 0 ≠ 0 := by
  rw [preparationUnit, preparationQuotientEval_zero, hq0, inv_one, mul_one]
  exact mul_ne_zero htop (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hr0.ne')))
end ClassicalComplexWPT
