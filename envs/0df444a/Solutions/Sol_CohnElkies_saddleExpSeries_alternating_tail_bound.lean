-- Prove2me | solution 1 for CohnElkies.saddleExpSeries_alternating_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/5c43ce20-973d-445b-84c7-1271fbd55611

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleExpSeries_hasSum
import Theorems.Thm_CohnElkies_saddleExpSeries_tail_term_le_geometric

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {y : ℝ} (hy : 0 ≤ y)
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1) :
    |Real.exp (-y) -
        (∑ n ∈ Finset.range m,
          (-y) ^ n / (n.factorial : ℝ))| ≤
      2 * (y ^ m / (m.factorial : ℝ)) := by
  let f : ℕ → ℝ := fun n =>
    (-y) ^ n / (n.factorial : ℝ)
  have hwhole : HasSum f (Real.exp (-y)) :=
    saddleExpSeries_hasSum (-y)
  have htail : Summable (fun n : ℕ => f (n + m)) :=
    (summable_nat_add_iff m).mpr hwhole.summable
  have hnorm : Summable
      (fun n : ℕ => ‖f (n + m)‖) := htail.norm
  have hgeometric :
      Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  have hmajor : Summable
      (fun n : ℕ =>
        (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ n)) :=
    hgeometric.mul_left (y ^ m / (m.factorial : ℝ))
  have hdecomp :
      (∑ n ∈ Finset.range m, f n) +
        (∑' n : ℕ, f (n + m)) = Real.exp (-y) :=
    HasSum.unique htail.hasSum.sum_range_add hwhole
  have htermnorm (n : ℕ) :
      ‖f (n + m)‖ =
        y ^ (m + n) / ((m + n).factorial : ℝ) := by
    try dsimp [f]
    rw [abs_div, abs_pow,
      abs_neg, abs_of_nonneg hy]
    have hfact : 0 < ((n + m).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + m)
    rw [abs_of_pos hfact]
    simp [Nat.add_comm]
  have hterms (n : ℕ) :
      ‖f (n + m)‖ ≤
        (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ n) := by
    rw [htermnorm n]
    exact saddleExpSeries_tail_term_le_geometric
      hy m hym n
  change |Real.exp (-y) -
    (∑ n ∈ Finset.range m, f n)| ≤
      2 * (y ^ m / (m.factorial : ℝ))
  have hidentity : Real.exp (-y) -
      (∑ n ∈ Finset.range m, f n) =
        ∑' n : ℕ, f (n + m) := by
    linarith
  calc
    |Real.exp (-y) -
        (∑ n ∈ Finset.range m, f n)| =
      ‖∑' n : ℕ, f (n + m)‖ := by
        rw [Real.norm_eq_abs, hidentity]
    _ ≤ ∑' n : ℕ, ‖f (n + m)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ n) :=
        Summable.tsum_le_tsum hterms hnorm hmajor
    _ = (y ^ m / (m.factorial : ℝ)) *
          (∑' n : ℕ, (1 / 2 : ℝ) ^ n) :=
        tsum_mul_left
    _ = 2 * (y ^ m / (m.factorial : ℝ)) := by
        rw [tsum_geometric_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)]
        norm_num; ring
end CohnElkies
