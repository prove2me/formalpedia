-- Prove2me | solution 1 for Erdos183.erdos_problem_183_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:36:49.45296+00:00
-- url     : https://prove2.me/submissions/cec0cfc6-e6d4-46a8-a53b-e4bf5b0a2ccd

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_Erdos183_divergentRamseyRoot
import Theorems.Thm_Erdos183_quantitativeLowerBound_explicit_all

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution :
    (∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ)) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop atTop := by
  exact ⟨quantitativeLowerBound_explicit_all, divergentRamseyRoot⟩
