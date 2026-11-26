-- Prove2me | solution 1 for ClassicalComplexWPT.evalL1PowerSeries_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:42.775076+00:00
-- url     : https://prove2.me/submissions/366da1e6-bac3-4bd7-822b-81198eb242df

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_tsum
import Theorems.Thm_ClassicalComplexWPT_summable_norm_l1_mul_pow
import Theorems.Thm_ClassicalComplexWPT_summable_l1_mul_pow
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (a b : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (convolution a b) w =
      evalL1PowerSeries a w * evalL1PowerSeries b w := by
  rw [evalL1PowerSeries_eq_tsum _ hw, evalL1PowerSeries_eq_tsum _ hw,
    evalL1PowerSeries_eq_tsum _ hw]
  let A : ℕ → ℂ := fun k ↦ a k * w ^ k
  let B : ℕ → ℂ := fun k ↦ b k * w ^ k
  have hA : Summable A := summable_l1_mul_pow a hw.le
  have hB : Summable B := summable_l1_mul_pow b hw.le
  have hAB : Summable (fun x : ℕ × ℕ ↦ A x.1 * B x.2) :=
    summable_mul_of_summable_norm
      (summable_norm_l1_mul_pow a hw.le) (summable_norm_l1_mul_pow b hw.le)
  rw [hA.tsum_mul_tsum_eq_tsum_sum_antidiagonal hB hAB]
  apply tsum_congr
  intro n
  rw [convolution_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  dsimp only [A, B]
  subst n
  rw [pow_add]
  ring
end ClassicalComplexWPT
