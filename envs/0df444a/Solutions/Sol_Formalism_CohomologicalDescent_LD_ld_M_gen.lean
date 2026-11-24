-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_M_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:37.348876+00:00
-- url     : https://prove2.me/submissions/2240ad15-41ed-4108-8650-ca6595aabd9e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector

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
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y j : ℕ) (hj : y + j ≤ w) : ((w - y).choose j : ℤ) • vec2 w y j ∈ ldM w y := Submodule.subset_span ⟨j, hj, rfl⟩
end Formalism.CohomologicalDescent.LD
