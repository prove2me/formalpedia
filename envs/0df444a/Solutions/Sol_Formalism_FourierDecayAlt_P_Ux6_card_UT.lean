-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.card_UT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:25:58.711801+00:00
-- url     : https://prove2.me/submissions/a541dda7-976e-4878-af45-d540db0be1f5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (j : ℕ) : Fintype.card (Formalism.FourierDecayAlt.G.UT j) ≤ j * j := by
  have := Fintype.card_subtype_le (fun q : Fin j × Fin j => q.1 < q.2)
  simpa [Fintype.card_prod] using this
end Formalism.FourierDecayAlt.P.Ux6
