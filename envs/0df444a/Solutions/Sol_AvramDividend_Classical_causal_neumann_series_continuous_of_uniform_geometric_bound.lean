-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_series_continuous_of_uniform_geometric_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:27:55.548642+00:00
-- url     : https://prove2.me/submissions/065d09e3-1aca-4bf1-88cf-12916e2460c6

import Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_series_continuousOn_nonnegative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- Uniform bounds B*ρ^n give a continuous causal Neumann sum on the closed half-line. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (B ρ : ℝ)
    (hB : 0 < B) (hρ : 0 < ρ) (hρone : ρ < 1)
    (hcont : ∀ n : ℕ, ContinuousOn (F n) (Ici (0 : ℝ)))
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |F n x| ≤ B * ρ ^ n) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x → Summable (fun n : ℕ => F n x)) := by
  have ha : 0 < ρ / B := div_pos hρ hB
  apply causal_neumann_geometric_series_continuousOn_nonnegative
    F (ρ / B) ρ ha (le_of_lt hρ) hρone hcont
  intro n x hx
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hBne : B ≠ 0 := ne_of_gt hB
  have hratio : ρ ^ (n + 1) / (ρ / B) = B * ρ ^ n := by
    rw [pow_succ]
    field_simp
  rw [hratio]
  exact hbound n x hx
