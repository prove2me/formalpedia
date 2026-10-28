-- Prove2me | solution 1 for AvramDividend.Classical.causal_reverse_Ioc_powers_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:50:56.360094+00:00
-- url     : https://prove2.me/submissions/a843eb48-b130-4d38-8995-1710948d3815

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_monotone_of_positive_kernel
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
import Mathlib.Order.Monotone.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The reverse-integrand recurrence is monotone by causal commutativity. -/
theorem solution
    (f : ℝ → ℝ) (U : ℕ → ℝ → ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hfcont : Continuous f)
    (hfmono : Monotone f)
    (hfpos : ∀ x : ℝ, 0 ≤ f x)
    (hUcont : ∀ n : ℕ, Continuous (U n))
    (hU0 : U 0 = f)
    (hUrec : ∀ n : ℕ, ∀ x : ℝ,
      U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) :
    ∀ n : ℕ, Monotone (U n) := by
  have hforward : ∀ n : ℕ, U (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * U n (x - s) ∂volume := by
    intro n
    funext x
    calc
      U (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume := hUrec n x
      _ = ∫ s in Ioc (0 : ℝ) x, U n s * f (x - s) ∂volume := by
        have heq : (fun s : ℝ => f (x - s) * U n s) =
            (fun s : ℝ => U n s * f (x - s)) := by
          funext s
          exact mul_comm _ _
        exact congrArg
          (fun g : ℝ → ℝ => ∫ s in Ioc (0 : ℝ) x, g s ∂volume) heq
      _ = ∫ s in Ioc (0 : ℝ) x, f s * U n (x - s) ∂volume :=
        (causal_Ioc_convolution_comm_all_real f (U n) x).symm
  exact causal_Ioc_convolution_powers_monotone_of_positive_kernel
    f U hfzero hfcont hfmono hfpos hUcont hU0 hforward
