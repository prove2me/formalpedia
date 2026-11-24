-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvRight_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:04.617474+00:00
-- url     : https://prove2.me/submissions/6ab28c6a-8f96-4137-90a7-5245c4c43b9c

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_qminor_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
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
theorem _root_.solution (hA : CapAdInv) : JF.CVRight := by
  intro k r E _ _ Y f hf y hy g hg
  have h1 := qminor_trn (k := k) (r := r) (ContinuousLinearMap.id ℂ E) gv_one hy (Q.EH k r) (EHc k r y)
    (fun c d f hf => EH_trn _ gv_one hy c d f hf)
    (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EHc_ck hy c d m f hf)
    (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f (by simpa [Q.mdim] using hf) g hg
  have e : trn (ContinuousLinearMap.id ℂ E) 1 y f = fun x => f (x * y) := by
    funext x; simp [trn]
  rw [e] at h1
  unfold Q.CV Q.capL
  rw [h1]
  simp only [trn, ContinuousLinearMap.id_apply, Matrix.one_mul]
  exact hA k r E y _ f hy hf (g * y) (gv_mul hg hy)
end Formalism.FourierDecayAlt.P.JFxB
