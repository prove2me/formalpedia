-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.psiQUnique_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:51.403866+00:00
-- url     : https://prove2.me/submissions/8bc30276-133c-4cc7-aa0c-a9ecb2294a39

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_dmin_sgs
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_cmin_gq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_zeta_gq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.PsiQUnique := by
  intro k r Wp Wq _ _ _ _ D p₁ p₂ q₁ q₂ h1 h2 hq1 hq2 he
  have hc : ∀ a, cmin k r D.z D.z' (sgs p₁ (gq D q₁)) a = cmin k r D.z D.z' (sgs p₂ (gq D q₂)) a := by
    intro a; rw [he]
  have hz : zeta k r D.z D.z' (sgs p₁ (gq D q₁)) = zeta k r D.z D.z' (sgs p₂ (gq D q₂)) := by rw [he]
  refine Prod.ext (funext fun a => ?_) ?_
  · have := hc a
    unfold cmin at this
    rw [BigCellZetaMinors.dmin_sgs D h1, BigCellZetaMinors.dmin_sgs D h1, BigCellZetaMinors.dmin_sgs D h2, BigCellZetaMinors.dmin_sgs D h2] at this
    rw [← BigCellZetaMinors.cmin_gq D hq1 a, ← BigCellZetaMinors.cmin_gq D hq2 a]
    exact this
  · unfold zeta at hz
    rw [BigCellZetaMinors.dmin_sgs D h1, BigCellZetaMinors.dmin_sgs D h1, BigCellZetaMinors.dmin_sgs D h2, BigCellZetaMinors.dmin_sgs D h2] at hz
    rw [← BigCellZetaMinors.zeta_gq D hq1, ← BigCellZetaMinors.zeta_gq D hq2]
    exact hz
end Formalism.FourierDecayAlt.P
