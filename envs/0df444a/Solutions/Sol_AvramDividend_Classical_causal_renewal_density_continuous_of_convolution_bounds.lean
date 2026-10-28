-- Prove2me | solution 1 for AvramDividend.Classical.causal_renewal_density_continuous_of_convolution_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:02:10.508126+00:00
-- url     : https://prove2.me/submissions/31062241-71e3-447e-92ff-c94927b3f888

import Theorems.Thm_AvramDividend_Classical_causal_l1_continuous_convolution_power_induction_with_tail_bounds
import Theorems.Thm_AvramDividend_Classical_continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound
import Mathlib.Analysis.Normed.Group.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Continuity of a positive-time renewal density series from causal convolution
and geometric bounds, with the zero-index shift explicit. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x)
      (Ioi (0 : ℝ)) := by
  have hFn :=
    causal_l1_continuous_convolution_power_induction_with_tail_bounds
      κ F ρ (le_of_lt hρ0) hκint hκcont hκzero hκbound
      hF0 hFsucc hFnonneg hFpoint
  let G : ℕ → ℝ → ℝ := fun n x =>
    if n = 0 then 0 else F (n - 1) x
  have hGc (n : ℕ) : ContinuousOn (G n) (Ioi (0 : ℝ)) := by
    cases n with
    | zero =>
        simpa [G] using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0))
    | succ n =>
        simpa [G] using hFn n
  have hGb (n : ℕ) (x : ℝ) (hx : 0 < x) :
      ‖G n x‖ ≤ ((n : ℝ) ^ 2 * ρ ^ n) / x := by
    cases n with
    | zero => simp [G]
    | succ n =>
        have hn : 0 ≤ F n x := hFnonneg n x (le_of_lt hx)
        simpa [G, Real.norm_eq_abs, abs_of_nonneg hn,
          Nat.cast_add, Nat.cast_one] using hFpoint n x hx
  exact continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound
    G ρ hρ0 hρ1 hGc hGb

