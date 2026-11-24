-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.card_LW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:33:05.358518+00:00
-- url     : https://prove2.me/submissions/0375e680-dd7a-4796-b8cf-61837200d868

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
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) : Fintype.card (LW σ) ≤ p * p := by
  have := Fintype.card_subtype_le (fun q : Fin p × Fin p => q.2 < q.1 ∧ σ.symm q.2 < σ.symm q.1)
  simpa [Fintype.card_prod] using this
end Formalism.FourierDecayAlt.P.Ux6
