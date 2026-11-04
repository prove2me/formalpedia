-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_k_rate_uniform_grid_algebra_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:17:27.865828+00:00
-- url     : https://prove2.me/submissions/4ad666a9-996a-43fe-ab8d-31845f18dc79

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Transfer a small-time real first-order rate to a uniform-grid
expectation with a fixed total horizon, via exact mesh normalisation. -/
theorem solution
    (δ : ℕ → ℝ) (F : ℝ → ℝ) (T L : ℝ)
    (hδ : Tendsto δ atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hδnz : ∀ n, δ n ≠ 0)
    (hmesh : ∀ n : ℕ, ((n : ℝ) + 1) * δ n = T)
    (hRate : Tendsto (fun h : ℝ => F h / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * F (δ n))
      atTop (nhds (T * L)) := by
  have hScaled :
      Tendsto (fun n : ℕ => T * (F (δ n) / δ n))
        atTop (nhds (T * L)) :=
    tendsto_const_nhds.mul (hRate.comp hδ)
  have hRewrite (n : ℕ) :
      ((n : ℝ) + 1) * F (δ n) =
        T * (F (δ n) / δ n) := by
    rw [← hmesh n]
    field_simp [hδnz n]
    <;> ring
  simpa only [hRewrite] using hScaled
