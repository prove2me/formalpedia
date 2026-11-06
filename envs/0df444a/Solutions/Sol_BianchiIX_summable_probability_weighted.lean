-- Prove2me | solution 1 for BianchiIX.summable_probability_weighted
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:07:49.115192+00:00
-- url     : https://prove2.me/submissions/73065a4a-5d31-4ac2-9142-67975988ec96

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX


theorem solution {ι : Type*} {p f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp : HasSum p 1) (hf : ∀ i, |f i| ≤ M) :
    Summable (fun i => p i * f i) := by
  apply (hp.summable.mul_right M).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 i)]
  exact mul_le_mul_of_nonneg_left (hf i) (hp0 i)
