-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:02.973807+00:00
-- url     : https://prove2.me/submissions/42c7ea9b-b0f5-4566-81b4-75da16371ab6

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_herm_bigCell
import Theorems.Thm_Formalism_QuantumDeterminants_bigCellMinors


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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BigCellZetaMinors
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    zeta k r D.z D.z' (gq D q) = q.2 := by
  have hz := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.2 hq.1
  rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, (D.sec.2 q.2 hq.2).2] at hz
  exact hz
end Formalism.FourierDecayAlt.P.BigCellZetaMinors
