-- Prove2me | solution 1 for BianchiIX.probability_mass_l1_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:10:30.90707+00:00
-- url     : https://prove2.me/submissions/58fc63ae-4250-4eb8-9c86-572691b354d0

import Theorems.Thm_BianchiIX_probability_mass_l1_identity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX


theorem solution {ι : Type*} {p : ℕ → ι → ℝ} {q : ι → ℝ}
    (hp0 : ∀ n i, 0 ≤ p n i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, |p n i - q i|) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => ∑' i, min (p n i) (q i)) atTop (𝓝 (∑' i, q i)) := by
    apply tendsto_tsum_of_dominated_convergence hq.summable
    · intro i
      simpa only [min_self] using (hpoint i).min
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q i) atTop (𝓝 (q i)))
    · exact Eventually.of_forall (fun n i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 n i) (hq0 i))]
        exact min_le_right _ _)
  rw [hq.tsum_eq] at hm
  simp_rw [probability_mass_l1_identity (hp0 _) hq0 (hp _) hq]
  simpa using (tendsto_const_nhds.sub (hm.const_mul 2) :
    Tendsto (fun n => (2 : ℝ) - 2 * ∑' i, min (p n i) (q i)) atTop (𝓝 (2 - 2 * 1)))
