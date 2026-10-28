-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_resolvent_identity_of_finite_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:12:24.091022+00:00
-- url     : https://prove2.me/submissions/075ec59e-9635-4c78-bf37-9fd602b34451

import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

open Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Pointwise convergence preserves a finite Neumann resolvent equation. -/
theorem solution
    (F g : ℝ → ℝ) (T : (ℝ → ℝ) → (ℝ → ℝ))
    (S Q : ℕ → ℝ → ℝ)
    (hfinite : ∀ n : ℕ, S n + T (S n) = F - Q (n + 1))
    (hS : ∀ x : ℝ, Tendsto (fun n : ℕ => S n x) atTop (nhds (g x)))
    (hTS : ∀ x : ℝ, Tendsto (fun n : ℕ => T (S n) x)
      atTop (nhds (T g x)))
    (hQ : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ))) :
    ∀ x : ℝ, g x + T g x = F x := by
  intro x
  have hsum : Tendsto (fun n : ℕ => S n x + T (S n) x)
      atTop (nhds (g x + T g x)) := (hS x).add (hTS x)
  have hleft : Tendsto (fun n : ℕ => F x - Q (n + 1) x)
      atTop (nhds (g x + T g x)) := by
    have heq : (fun n : ℕ => F x - Q (n + 1) x) =
        (fun n : ℕ => S n x + T (S n) x) := by
      funext n
      exact (congrFun (hfinite n) x).symm
    rw [heq]
    exact hsum
  have hconst : Tendsto (fun _ : ℕ => F x) atTop (nhds (F x)) :=
    tendsto_const_nhds
  have hright : Tendsto (fun n : ℕ => F x - Q (n + 1) x)
      atTop (nhds (F x)) := by
    simpa using hconst.sub (hQ x)
  exact tendsto_nhds_unique hleft hright
