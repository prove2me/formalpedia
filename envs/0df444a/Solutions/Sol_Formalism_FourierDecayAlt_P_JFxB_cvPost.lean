-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvPost
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:11:45.914113+00:00
-- url     : https://prove2.me/submissions/eeca665e-51b8-4632-a383-e204d38650ee

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_qminor_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_trn_one_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution : JF.CVPost := by
  intro k r E E' _ _ _ _ Y Φ f hf g hg
  have h1 := qminor_trn (k := k) (r := r) Φ gv_one gv_one (Q.EH k r) (Q.EH k r)
    (fun c d f hf => by
      intro g hg
      rw [EH_trn Φ gv_one gv_one c d f hf g hg, EHc_one])
    (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EH_ck c d m f hf)
    (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f (by simpa [Q.mdim] using hf) g hg
  rw [trn_one_one, trn_one_one] at h1
  exact h1
end Formalism.FourierDecayAlt.P.JFxB
