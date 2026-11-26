-- Prove2me | solution 1 for ClassicalComplexWPT.summable_norm_l1_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:43.642202+00:00
-- url     : https://prove2.me/submissions/d600153a-3396-490a-90db-884600c91be2

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries

set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (a : L1Sequence) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k : ℕ ↦ ‖a k * w ^ k‖) := by
  exact (L1Coeff.summable_norm a).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw))
end ClassicalComplexWPT
