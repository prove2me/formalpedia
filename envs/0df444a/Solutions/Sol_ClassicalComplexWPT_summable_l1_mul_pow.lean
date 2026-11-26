-- Prove2me | solution 1 for ClassicalComplexWPT.summable_l1_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:37.661841+00:00
-- url     : https://prove2.me/submissions/662d418e-8d32-4d06-bf08-0314c91c0184

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Theorems.Thm_ClassicalComplexWPT_summable_norm_l1_mul_pow

set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (a : L1Sequence) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k : ℕ ↦ a k * w ^ k) :=
  Summable.of_norm (summable_norm_l1_mul_pow a hw)
end ClassicalComplexWPT
