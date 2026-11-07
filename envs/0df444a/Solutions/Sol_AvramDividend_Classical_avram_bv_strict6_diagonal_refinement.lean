-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_diagonal_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:31:54.52544+00:00
-- url     : https://prove2.me/submissions/d9e32508-60f2-4f30-b464-d65913356aaa

import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology
noncomputable section

/-- Select increasingly fine physical mesh indices across expanding localisations. -/
theorem solution
    (E : ℕ → ℕ → ℝ)
    (hvanish : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ,
      (∀ k, k ≤ φ k) ∧
      (∀ k, |E k (φ k)| < 1 / ((k : ℝ) + 1)) := by
  classical
  have hchoice (k : ℕ) :
      ∃ n : ℕ, k ≤ n ∧
        |E k n| < 1 / ((k : ℝ) + 1) := by
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hErr : ∀ᶠ n : ℕ in atTop,
        |E k n| < 1 / ((k : ℝ) + 1) := by
      have hDist := (Metric.tendsto_nhds.mp (hvanish k)) _ hpos
      simpa [Real.dist_eq] using hDist
    have hGe : ∀ᶠ n : ℕ in atTop, k ≤ n :=
      Filter.eventually_ge_atTop k
    obtain ⟨n, hn⟩ := (hGe.and hErr).exists
    exact ⟨n, hn.1, hn.2⟩
  choose φ hφ using hchoice
  exact ⟨φ, (fun k => (hφ k).1), (fun k => (hφ k).2)⟩
