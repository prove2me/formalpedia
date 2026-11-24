-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.evaluation_congruence_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:54.935806+00:00
-- url     : https://prove2.me/submissions/dc493475-e364-43a2-acf2-25b27a707736

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : EvalCong := by
  intro O _ lam a g hg
  obtain ⟨q, hq⟩ := hg
  have hc : constantCoeff g = a + lam * (-constantCoeff q) := by
    have h2 := congrArg constantCoeff hq
    simp only [map_sub, map_mul, constantCoeff_C, constantCoeff_X] at h2
    linear_combination h2
  refine ⟨⟨-constantCoeff q, hc⟩, ?_⟩
  intro k _ red hred
  rw [hc, map_add, map_mul, hred, zero_mul, add_zero]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
