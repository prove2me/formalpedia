-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.erdos_problem_183_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/603dfde6-55ec-408c-afcd-b5436da3bcab

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_quantitativeLowerBound_explicit_all
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_divergentRamseyRoot

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution :
    (∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ)) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop atTop := by
  exact ⟨quantitativeLowerBound_explicit_all, divergentRamseyRoot⟩
end ErdosProblems.MulticolourTriangleRamsey
