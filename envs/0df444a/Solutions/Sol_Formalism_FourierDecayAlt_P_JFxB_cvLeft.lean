-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:45.396907+00:00
-- url     : https://prove2.me/submissions/aa8e216e-6733-40d1-86f6-392c41a17848

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_quantum_minor_left_hermitian


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
theorem _root_.solution : JF.CVLeft := by
  intro k r E _ _ Y f _ y _ g _
  unfold Q.CV Q.capL
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E (2 * r + k + 1) _ (Hpk k r) f (Q.posL k r 0) (Q.posL k r 0)
    (Q.uC k r 0 Y) y) g
end Formalism.FourierDecayAlt.P.JFxB
