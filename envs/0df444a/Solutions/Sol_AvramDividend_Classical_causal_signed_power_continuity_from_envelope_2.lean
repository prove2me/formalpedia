-- Prove2me | solution 2 for AvramDividend.Classical.causal_signed_power_continuity_from_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:56:26.236477+00:00
-- url     : https://prove2.me/submissions/d0e8b646-8470-48fa-86ba-ad5574f36599

import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support
import Theorems.Thm_AvramDividend_Classical_causal_signed_L1_convolution_powers_continuous_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Envelope bounds transfer positive-time continuity to signed powers. -/
theorem solution
    (k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hP0 : P 0 = k)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ)) := by
  have hPzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → P n x = 0 := by
    intro n x hx
    cases n with
    | zero => simpa [hP0] using hkzero x hx
    | succ n =>
        simpa [Set.Ioc_eq_empty_of_le hx] using congrFun (hPrec n) x
  have hBound : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |P n x| ≤ M := by
    intro n ε hε
    refine ⟨((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / ε, ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hε hx
    calc
      |P n x| ≤ F n x := hDom n x hxpos.le
      _ ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x :=
        hFpoint n x hxpos
      _ ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / ε := by
        gcongr
  have hkbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |k x| ≤ M := by
    intro ε hε
    rcases hBound 0 ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx
    simpa [hP0] using hM x hx
  have hPint : ∀ n : ℕ, Integrable (P n) volume := by
    intro n
    exact causal_positive_l1_global_integrable (P n) (hPL1 n) (hPzero n)
  have hPfull : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * P n (x - y) ∂volume := by
    intro n
    funext x
    calc
      P (n + 1) x = ∫ s in Ioc (0 : ℝ) x,
          k s * P n (x - s) ∂volume := congrFun (hPrec n) x
      _ = ∫ y : ℝ, k y * P n (x - y) ∂volume :=
        (causal_real_convolution_equals_positive_interval_under_support
          k (P n) hkzero (hPzero n) x).symm
  have hkint : Integrable k volume :=
    causal_positive_l1_global_integrable k hkL1 hkzero
  exact causal_signed_L1_convolution_powers_continuous_positive
    k P hkint hkcont hkzero hkbound hP0 hPfull hPint hPzero hBound
