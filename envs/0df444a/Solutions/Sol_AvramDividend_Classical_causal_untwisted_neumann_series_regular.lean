-- Prove2me | solution 1 for AvramDividend.Classical.causal_untwisted_neumann_series_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:43:28.267386+00:00
-- url     : https://prove2.me/submissions/337bc921-6709-45b1-9f83-0e07704b319f

import Theorems.Thm_AvramDividend_Classical_pointwise_summable_monotone_tsum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- An Esscher tilt transfers Neumann-series regularity to the undamped sum. -/
theorem solution
    (F U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hFsum : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFcont : ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici 0))
    (hrel : ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x)
    (hUmono : ∀ n : ℕ, Monotone (U n)) :
    (∀ x : ℝ, Summable (fun n : ℕ => U n x)) ∧
      ContinuousOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) ∧
      MonotoneOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) := by
  have hrecip (x : ℝ) :
      Real.exp (θ * x) * Real.exp (-(θ * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hUeq (n : ℕ) (x : ℝ) :
      U n x = Real.exp (θ * x) * F n x := by
    calc
      U n x = 1 * U n x := (one_mul _).symm
      _ = (Real.exp (θ * x) * Real.exp (-(θ * x))) * U n x := by
        rw [hrecip]
      _ = Real.exp (θ * x) * F n x := by rw [hrel]; ring
  have hUsum (x : ℝ) : Summable (fun n : ℕ => U n x) := by
    simpa only [hUeq] using
      (hFsum x).mul_left (Real.exp (θ * x))
  have hUtsum (x : ℝ) :
      (∑' n : ℕ, U n x) =
        Real.exp (θ * x) * (∑' n : ℕ, F n x) := by
    simp_rw [hUeq]
    rw [tsum_mul_left]
  have hE : ContinuousOn
      (fun x : ℝ => Real.exp (θ * x)) (Ici (0 : ℝ)) := by
    fun_prop
  have hUcont : ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) := by
    exact (hE.mul hFcont).congr (fun x hx => hUtsum x)
  have hUmon : Monotone
      (fun x : ℝ => ∑' n : ℕ, U n x) :=
    pointwise_summable_monotone_tsum U hUmono hUsum
  exact ⟨hUsum, hUcont, hUmon.monotoneOn _⟩