-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.lpa_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:51.815962+00:00
-- url     : https://prove2.me/submissions/96512ddf-4b11-49d4-bdfb-e89d31c8399f

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    {T : Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N} (h : FormMod T B) (x : N) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (h.pos x hx).le
end Formalism.CohomologicalDescent.LP
