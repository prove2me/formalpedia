-- Prove2me | solution 1 for CompactnessConjecture.four_cycle_uniform_manuscript_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/a163ee35-0a87-4ffb-a0e5-13c75014e764

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_four_cycle_free
import Theorems.Thm_CompactnessConjecture_cycleGraph_no_isolated
import Theorems.Thm_CompactnessConjecture_quadrangle_uniform_lower_of_prime_power_avoidance

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 4)
    (by simpa using cycleGraph_no_isolated 2)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_four_cycle_free _) hn
end CompactnessConjecture
