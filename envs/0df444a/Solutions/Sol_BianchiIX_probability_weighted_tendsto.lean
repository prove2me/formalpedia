-- Prove2me | solution 1 for BianchiIX.probability_weighted_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:12:46.706365+00:00
-- url     : https://prove2.me/submissions/7d86346c-2fd2-44e3-9e6e-4a1b213a260a

import Theorems.Thm_BianchiIX_probability_mass_l1_tendsto
import Theorems.Thm_BianchiIX_probability_weighted_difference_le
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX


theorem solution {ι : Type*} {p : ℕ → ι → ℝ} {q f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ n i, 0 ≤ p n i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i)))
    (hf : ∀ i, |f i| ≤ M) :
    Tendsto (fun n => ∑' i, p n i * f i) atTop (𝓝 (∑' i, q i * f i)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm
  · intro n
    exact probability_weighted_difference_le (hp0 n) hq0 (hp n) hq hf
  · simpa only [mul_zero] using (probability_mass_l1_tendsto hp0 hq0 hp hq hpoint).const_mul M
