-- Prove2me | solution 1 for CompactnessConjecture.six_cycle_eventual_manuscript_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/82904ccf-e1bd-44fb-bfd8-5a540aaf3499

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_six_cycle_uniform_manuscript_lower

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    six_cycle_uniform_manuscript_lower hn
end CompactnessConjecture
