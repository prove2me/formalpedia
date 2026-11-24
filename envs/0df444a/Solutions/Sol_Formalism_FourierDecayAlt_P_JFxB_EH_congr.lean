-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.EH_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:42.921018+00:00
-- url     : https://prove2.me/submissions/404f9814-291e-461c-865b-028da86fe8a2

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr


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
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (c d : Fin (2 * r + k + 1)) (f f₂ : Mat k r → E) (h : ∀ g ∈ GV k r, f g = f₂ g) :
    ∀ g ∈ GV k r, Q.EH k r c d f g = Q.EH k r c d f₂ g := by
  intro g hg
  rw [EH_eq, EH_eq]
  simp only
  rw [Dx_congr (x := (false, Xa k r c d)) (Xa_lie c d) h g hg, Dx_congr (x := (false, Xb k r c d)) (Xb_lie c d) h g hg]
end Formalism.FourierDecayAlt.P.JFxB
