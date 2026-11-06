-- Prove2me | solution 1 for BianchiIX.probability_weighted_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:10:51.447233+00:00
-- url     : https://prove2.me/submissions/e434f6f2-c583-4703-99c0-ef55ecb3bb27

import Theorems.Thm_BianchiIX_summable_probability_weighted
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX


theorem solution {ι : Type*} {p q f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1)
    (hf : ∀ i, |f i| ≤ M) :
    |(∑' i, p i * f i) - ∑' i, q i * f i| ≤ M * ∑' i, |p i - q i| := by
  have hpf := summable_probability_weighted hp0 hp hf
  have hqf := summable_probability_weighted hq0 hq hf
  have hdiff := (hp.summable.sub hq.summable).abs
  have hdom : Summable (fun i => M * |p i - q i|) := hdiff.mul_left M
  have habs : Summable (fun i => |p i * f i - q i * f i|) := (hpf.sub hqf).abs
  rw [← hpf.tsum_sub hqf]
  calc
    |∑' i, (p i * f i - q i * f i)| ≤ ∑' i, |p i * f i - q i * f i| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => p i * f i - q i * f i)
          (by simpa only [Real.norm_eq_abs] using habs))
    _ ≤ ∑' i, M * |p i - q i| := by
      apply habs.tsum_le_tsum _ hdom
      intro i
      rw [← sub_mul, abs_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
    _ = _ := tsum_mul_left
