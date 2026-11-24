-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:24.556821+00:00
-- url     : https://prove2.me/submissions/268b8e08-9297-45b3-b835-4ad74ba59051

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (Cs : Finset (Fin r)) (μ : Fin Cs.card → ℤ) : ∃ la : Fin r → ℤ, la ∘ enumC Cs = μ :=
  ⟨Function.extend (enumC Cs) μ 0, Function.extend_comp (enumC Cs).injective μ 0⟩
end Formalism.InvariantFactorPaths.PW
