-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_C2_of_corrected_neumann_series_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:13:24.875343+00:00
-- url     : https://prove2.me/submissions/8cf39348-8ede-498d-932d-7397e57937b9

import Theorems.Thm_AvramDividend_Classical_causal_neumann_full_resolvent_regular_of_correction_bounds
import Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The signed Neumann correction proves C2 for the integrated Volterra
solution once its exact resolvent equation has been established. -/
theorem solution
    (K V : ℝ → ℝ) (P H : ℕ → ℝ → ℝ) (a β ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R))
    (hEq : ∀ x : ℝ, 0 < x →
      a * (1 / a + Real.exp (w * x) * (∑' n : ℕ, H n x)) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (1 / a + Real.exp (w * s) *
              (∑' n : ℕ, H n s)) ∂volume) = 1) :
    ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) := by
  obtain ⟨g, hform, hg0, hg1⟩ :=
    causal_neumann_full_resolvent_regular_of_correction_bounds
      P H a ρ w ha hρ0 hρ1 hw hP hH hHcont hHasDeriv hCont
  apply causal_volterra_C2_of_C1_derivative_resolvent
    K g V a β ha hK hVc hVb hVe hg0 hg1
  intro x hx
  simpa only [hform] using hEq x hx
