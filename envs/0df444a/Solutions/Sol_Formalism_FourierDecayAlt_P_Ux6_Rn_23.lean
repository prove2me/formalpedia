-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.Rn_23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:35:00.644847+00:00
-- url     : https://prove2.me/submissions/16bf3f9b-1f34-4ac4-a76b-ca60f63e4896

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block3_apply

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
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (x : RC k j ρ) (i : Fin (2 * ρ + k + 1)) (b : Fin j) :
    Rn k j ρ x (eB k j ρ (Sum.inl (Sum.inr i))) (eB k j ρ (Sum.inr b)) = x.1 i b := by
  simp [Rn, block3_apply]
end Formalism.FourierDecayAlt.P.Ux6
