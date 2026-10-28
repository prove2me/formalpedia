-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_local_to_pointwise_geom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:26:50.688655+00:00
-- url     : https://prove2.me/submissions/a3e0fd58-556e-4cde-9ba2-7779e08093c7

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Positive-time local bounds and causal zero extension imply pointwise bounds. -/
theorem solution
    (Q : ℕ → ℝ → ℝ) (a ρ : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → Q (n + 1) x = 0)
    (hLocal : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖Q n s‖ ≤ C * ρ ^ n) :
    ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n := by
  intro x
  by_cases hx : 0 < x
  · obtain ⟨C, hC, h⟩ := hLocal x
    refine ⟨C, hC, ?_⟩
    intro n
    exact h n x (mem_Ioc.mpr ⟨hx, le_refl x⟩)
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    have ha0 : 0 ≤ 1 / a := (one_div_pos.mpr ha).le
    refine ⟨1 / a, ha0, ?_⟩
    intro n
    cases n with
    | zero =>
        rw [congrFun hQ0 x]
        simpa only [pow_zero, mul_one, Real.norm_eq_abs,
          abs_of_nonneg ha0] using (le_refl (1 / a))
    | succ n =>
        have hzero' := hzero n x hx0
        simpa only [Nat.succ_eq_add_one, hzero', norm_zero] using
          (mul_nonneg ha0 (pow_nonneg hρ0 (n + 1)))
