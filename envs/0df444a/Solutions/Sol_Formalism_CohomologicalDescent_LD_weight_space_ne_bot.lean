-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.weight_space_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:15.316414+00:00
-- url     : https://prove2.me/submissions/d5086e51-acef-474e-878a-335643644935

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} {ν μ : Fin r → ℕ} {x : MvPolynomial (Fin r × Fin r) ℤ} (hx : x ∈ nablaWt r ν μ)
    (hne : x ≠ 0) : nablaWt r ν μ ≠ ⊥ := by
  intro h
  rw [h] at hx
  exact hne ((Submodule.mem_bot _).1 hx)
end Formalism.CohomologicalDescent.LD
