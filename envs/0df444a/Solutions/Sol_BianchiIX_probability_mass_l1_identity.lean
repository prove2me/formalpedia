-- Prove2me | solution 1 for BianchiIX.probability_mass_l1_identity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:07:45.126184+00:00
-- url     : https://prove2.me/submissions/eb303167-0fe1-45e7-923a-35d183dd6d97

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX

private theorem BianchiIX.abs_sub_eq_add_sub_min (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem solution {ι : Type*} {p q : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1) :
    (∑' i, |p i - q i|) = 2 - 2 * ∑' i, min (p i) (q i) := by
  have hm : Summable (fun i => min (p i) (q i)) :=
    Summable.of_nonneg_of_le (fun i => le_min (hp0 i) (hq0 i)) (fun i => min_le_right _ _) hq.summable
  simp_rw [abs_sub_eq_add_sub_min]
  rw [(hp.summable.add hq.summable).tsum_sub (hm.mul_left 2),
    hp.summable.tsum_add hq.summable, tsum_mul_left, hp.tsum_eq, hq.tsum_eq]
  ring
