-- Prove2me | solution 1 for ContDiff.exists_weighted_cutoff_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T15:49:14.520266+00:00
-- url     : https://prove2.me/submissions/db728995-460a-46e7-b995-c4c60b5997d6

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open Filter
open scoped ContDiff Topology
set_option autoImplicit false

theorem solution (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q)
    (hlo : ∀ s : ℝ, s ≤ 1 → q s = 0)
    (hhi : ∀ s : ℝ, 2 ≤ s → q s = 1) (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, ‖iteratedDeriv r q s‖ * ‖s‖ ^ r ≤ D := by
  have hcont := (hq.continuous_iteratedDeriv r (by
    exact WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ ⊤))).mul (continuous_id.pow r)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max A 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro s
  by_cases hs : s ∈ Set.Icc (1 : ℝ) 2
  · simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, norm_mul, norm_pow] using (hA s hs).trans (le_max_left A 1)
  · have htail : q =ᶠ[𝓝 s] (fun _ => if s < 1 then (0 : ℝ) else 1) := by
      by_cases hl : s < 1
      · filter_upwards [Iio_mem_nhds hl] with t ht
        simp [hl, hlo t (le_of_lt ht)]
      · have hh : 2 < s := by simp only [Set.mem_Icc, not_and_or] at hs; rcases hs with h|h <;> linarith
        filter_upwards [Ioi_mem_nhds hh] with t ht
        simp [hl, hhi t (le_of_lt ht)]
    rw [htail.iteratedDeriv_eq r, iteratedDeriv_const]
    by_cases hr : r = 0
    · subst r
      simp only [if_true, pow_zero, mul_one]
      split_ifs <;> simp [le_max_right A 1]
    · simp [hr, le_trans zero_le_one (le_max_right A 1)]
