-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_integral_resolvent_of_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:18:12.500219+00:00
-- url     : https://prove2.me/submissions/938a506c-ea45-470e-9653-824681f008f0

import Mathlib.Topology.Defs.Filter
import Mathlib.Algebra.BigOperators.Pi
import Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_integral_telescope
import Theorems.Thm_AvramDividend_Classical_causal_neumann_resolvent_identity_of_finite_convergence

open AvramDividend.Classical MeasureTheory Set Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Convergent finite causal Neumann identities give the integral resolvent. -/
theorem solution
    (a : ℝ) (B F g : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume)
    (hS : ∀ x : ℝ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) x)
      atTop (nhds (g x)))
    (hTS : ∀ x : ℝ, Tendsto
      (fun n : ℕ => (1 / a) * (∫ s in Ioc (0 : ℝ) x,
        B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s ∂volume))
      atTop (nhds ((1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume))))
    (hQ : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ))) :
    ∀ x : ℝ, g x + (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) = F x := by
  classical
  let T : (ℝ → ℝ) → (ℝ → ℝ) :=
    fun f x => (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * f s ∂volume)
  let S : ℕ → ℝ → ℝ :=
    fun n => ∑ i ∈ Finset.range (n + 1), Q i
  have hfinite (n : ℕ) : S n + T (S n) = F - Q (n + 1) := by
    simpa only [S, T, Finset.sum_apply] using
      (causal_neumann_finite_integral_telescope a B F Q hzero hstep hI n)
  exact causal_neumann_resolvent_identity_of_finite_convergence
    F g T S Q hfinite hS hTS hQ
