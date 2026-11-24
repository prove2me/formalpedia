-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:06:05.426925+00:00
-- url     : https://prove2.me/submissions/1547e0cd-1fb9-4de7-91db-a3e0846ce413

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellZetaMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.BigCellZetaMinors
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => by simp, by simp⟩
  simp [UH]
end Formalism.FourierDecayAlt.P.BigCellZetaMinors
