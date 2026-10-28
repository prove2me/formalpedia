-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_geometric_correction_contDiffOn_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:52:25.840543+00:00
-- url     : https://prove2.me/submissions/ad78271d-10f0-4464-abc1-520b18cd00aa

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_local_open_intervals
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- Geometric control of the primitive terms supplies the missing basepoint
summability and patches the local derivative estimates to global C1. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R)) :
    ContDiffOn ℝ 1 (fun y : ℝ => ∑' n : ℕ, H n y)
      (Ioi (0 : ℝ)) := by
  have hρnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact hρ1
  have hgeom : Summable (fun n : ℕ => ρ ^ n) :=
    summable_geometric_of_norm_lt_one hρnorm
  have hmajor : Summable (fun n : ℕ => (ρ / a) * ρ ^ n) :=
    hgeom.mul_left (ρ / a)
  have hval : ∀ y : ℝ, 0 < y → Summable (fun n : ℕ => H n y) := by
    intro y hy
    apply Summable.of_norm_bounded hmajor
    intro n
    rw [Real.norm_eq_abs]
    calc
      |H n y| ≤ ρ ^ (n + 1) / a := hH n y hy.le
      _ = (ρ / a) * ρ ^ n := by rw [pow_succ]; ring
  apply contDiffOn_one_Ioi_of_local_open_intervals
  intro x hx
  have hε : 0 < x / 2 := by linarith
  have hεx : x / 2 < x := by linarith
  have hxR : x < x + 1 := by linarith
  refine ⟨x / 2, x + 1, hε, hεx, hxR, ?_⟩
  exact causal_neumann_series_C1_of_signed_power_bounds
    P H a (x / 2) (x + 1) ρ w
    ha hε hρ0 hρ1 hw
    (hP (x / 2) hε)
    (fun n y hy => hH n y (le_trans hε.le hy))
    (hHasDeriv (x / 2) hε)
    (hCont (x / 2) (x + 1) hε)
    x ⟨hεx, hxR⟩ (hval x hx)
