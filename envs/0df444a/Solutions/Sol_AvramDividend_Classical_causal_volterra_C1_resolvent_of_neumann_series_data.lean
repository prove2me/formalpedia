-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_C1_resolvent_of_neumann_series_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:33:20.164885+00:00
-- url     : https://prove2.me/submissions/26b961ff-9fe8-487c-9d31-5557c22b16ac

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_local_open_intervals
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A geometrically controlled signed Neumann sum solves the C1 derivative
resolvent problem once its Volterra equation and boundary continuity hold. -/
theorem solution
    (K : ℝ → ℝ) (P H : ℕ → ℝ → ℝ) (a β ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R))
    (hval : ∀ y : ℝ, 0 < y → Summable (fun n : ℕ => H n y))
    (hg0 : ContinuousOn (fun y : ℝ => ∑' n : ℕ, H n y) (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * (∑' n : ℕ, H n x) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * (∑' n : ℕ, H n s) ∂volume) = 1) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by
  refine ⟨(fun y : ℝ => ∑' n : ℕ, H n y), hg0, ?_, hgeq⟩
  apply contDiffOn_one_Ioi_of_local_open_intervals
  intro x hx
  have hε : 0 < x / 2 := by linarith
  have hεx : x / 2 < x := by linarith
  have hxR : x < x + 1 := by linarith
  refine ⟨x / 2, x + 1, hε, hεx, hxR, ?_⟩
  exact causal_neumann_series_C1_of_signed_power_bounds
    P H a (x / 2) (x + 1) ρ w
    ha hε hρ0 hρ1 hw
    (hP (x / 2) hε) (hH (x / 2) hε)
    (hHasDeriv (x / 2) hε) (hCont (x / 2) (x + 1) hε)
    x ⟨hεx, hxR⟩ (hval x hx)
