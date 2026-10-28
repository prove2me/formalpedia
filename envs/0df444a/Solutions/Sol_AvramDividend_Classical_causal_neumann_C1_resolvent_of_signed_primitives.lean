-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_C1_resolvent_of_signed_primitives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:00:10.311281+00:00
-- url     : https://prove2.me/submissions/226e9153-4155-44f8-a3fc-5b6ffbafae55

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_derivative_from_positive_L1
import Theorems.Thm_AvramDividend_Classical_causal_neumann_full_resolvent_regular_of_correction_bounds
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Signed L1 power continuity gives derivatives of the Neumann correction primitives. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hPbound : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hHbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hHdef : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P n s ∂volume)) / a)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPcont : ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ))) :
    ∃ g : ℝ → ℝ,
      (g = fun y : ℝ => 1 / a +
        Real.exp (w * y) * (∑' n : ℕ, H n y)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by
  have hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x := by
    intro ε hε n x hx
    have hxpos : 0 < x := lt_of_lt_of_le hε hx
    have h := causal_scaled_primitive_derivative_from_positive_L1
      (P n) a w (hPL1 n) (hPcont n) x hxpos
    simpa only [hHdef n] using h
  have hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x)
        (Ioo ε R) := by
    intro ε R hε n
    have hPos : Ioo ε R ⊆ Ioi (0 : ℝ) := by
      intro x hx
      exact lt_trans hε hx.1
    have hNonneg : Ioo ε R ⊆ Ici (0 : ℝ) := by
      intro x hx
      exact le_of_lt (lt_trans hε hx.1)
    have hPterm : ContinuousOn (fun x : ℝ => P n x / a) (Ioo ε R) :=
      ((hPcont n).mono hPos).div_const a
    have hHterm : ContinuousOn (fun x : ℝ => w * H n x) (Ioo ε R) :=
      continuousOn_const.mul ((hHcont n).mono hNonneg)
    exact hPterm.sub hHterm
  exact causal_neumann_full_resolvent_regular_of_correction_bounds
    P H a ρ w ha hρ0 hρ1 hw hPbound hHbound hHcont hHasDeriv hCont
