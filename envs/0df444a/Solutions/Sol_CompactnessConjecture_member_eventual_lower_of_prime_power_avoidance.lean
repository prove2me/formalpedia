-- Prove2me | solution 1 for CompactnessConjecture.member_eventual_lower_of_prime_power_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/17722c47-3e8b-46cc-9294-d299082cb9a6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_member_no_isolated
import Theorems.Thm_CompactnessConjecture_quadrangle_uniform_lower_of_prime_power_avoidance

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution
    {forbidden : FiniteGraph}
    (hmember : forbidden ∈ proposedFamily)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.graph.Free
        (symplecticQuadrangle (GaloisField t j))) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount t)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    quadrangle_uniform_lower_of_prime_power_avoidance
      forbidden.graph
      (proposedFamily_member_no_isolated hmember)
      t ht htgap hfree hn
end CompactnessConjecture
