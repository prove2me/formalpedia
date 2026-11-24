-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.weightedSum_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:09.698507+00:00
-- url     : https://prove2.me/submissions/64e99e2c-c785-42fd-8487-743dac3309e7

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_Icc_eq_add_sum_Ioc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (f : ℕ → ℂ) {y Y : ℝ} (hyY : y ≤ Y) :
    (y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y
      = ((Y - y : ℝ) : ℂ) * partialSumUpTo f y
        + ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ) := by
  unfold weightedPartialSumUpTo partialSumUpTo
  rw [sum_Icc_eq_add_sum_Ioc _ (Nat.floor_mono hyY)]
  simp only [mul_add, Finset.mul_sum]
  rw [show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring, ← Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring
end Formalism.ZeroFreeDirichlet
