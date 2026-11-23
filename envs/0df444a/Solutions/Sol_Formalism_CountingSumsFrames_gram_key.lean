-- Prove2me | solution 1 for Formalism.CountingSumsFrames.gram_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:43.006018+00:00
-- url     : https://prove2.me/submissions/4b3c4d6f-4110-4974-bc75-dbb02ce03fef

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Real
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : (n : ℝ) * x ≤ y) :
    (1 - y) * (1 + x) ^ n ≤ 1 := by
  have hp : 0 ≤ (1 + x) ^ n := by positivity
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    have e1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have e2 : (1 + x) ^ n ≤ Real.exp (n * x) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
    calc (1 - y) * (1 + x) ^ n ≤ Real.exp (-y) * Real.exp (n * x) :=
          mul_le_mul e1 e2 hp (Real.exp_pos _).le
      _ = Real.exp (n * x - y) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
end Formalism.CountingSumsFrames
