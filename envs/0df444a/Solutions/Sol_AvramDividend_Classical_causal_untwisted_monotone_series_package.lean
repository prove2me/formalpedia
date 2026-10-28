-- Prove2me | solution 1 for AvramDividend.Classical.causal_untwisted_monotone_series_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:19:28.852172+00:00
-- url     : https://prove2.me/submissions/d35033e1-b129-44de-9493-cc0e8a5cabe4

import Theorems.Thm_AvramDividend_Classical_causal_exponential_convolution_power_untwist
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_powers_continuity
import Theorems.Thm_AvramDividend_Classical_causal_reverse_Ioc_powers_monotone
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_neumann_series_regular
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Reverse the Esscher tilt and inherit monotonicity and continuity of the renewal series. -/
theorem solution
    (f K : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ : ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hfcont : Continuous f) (hfpos : ∀ x : ℝ, 0 ≤ f x)
    (hfmono : Monotone f)
    (hK : ∀ x : ℝ, K x = Real.exp (-(θ * x)) * f x)
    (hF0 : F 0 = K)
    (hFrec : ∀ n : ℕ, ∀ x : ℝ, F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * F n s ∂volume)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hFsum : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFseriescont : ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici 0)) :
    ∃ U : ℕ → ℝ → ℝ,
      U 0 = f ∧
      (∀ n : ℕ, ∀ x : ℝ, U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ,
        F n x = Real.exp (-(θ * x)) * U n x) ∧
      (∀ n : ℕ, Continuous (U n)) ∧
      (∀ n : ℕ, Monotone (U n)) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => U n x)) ∧
      ContinuousOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) ∧
      MonotoneOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) := by
  let U : ℕ → ℝ → ℝ :=
    Nat.rec f (fun _ g => fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume)
  have hU0 : U 0 = f := rfl
  have hUrec : ∀ n : ℕ, ∀ x : ℝ, U (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume := by
    intro n x
    rfl
  have hrel :=
    causal_exponential_convolution_power_untwist
      f K F U θ hK hF0 hFrec hU0 hUrec
  have hUcont :=
    causal_untwisted_powers_continuity F U θ hFcont hrel
  have hUmono :=
    causal_reverse_Ioc_powers_monotone
      f U hfzero hfcont hfmono hfpos hUcont hU0 hUrec
  obtain ⟨hsum, hcont, hmono⟩ :=
    causal_untwisted_neumann_series_regular
      F U θ hFsum hFseriescont hrel hUmono
  exact ⟨U, hU0, hUrec, hrel, hUcont, hUmono,
    hsum, hcont, hmono⟩
