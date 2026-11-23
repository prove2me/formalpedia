-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.weight_model_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:19.669176+00:00
-- url     : https://prove2.me/submissions/3a66f8f9-1dfc-4378-82d4-ee29bef24547

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_wExact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) :
    W1 (Icc 1 (P.k - 1)) (rc P π) (C (-((P.T : ℂ) * P.T')) * q1P P) (wNum P π /ₘ coordinatePolynomial P π)
      (fun l => ((Nrm P l π : ℝ) : ℂ)) := by
  have := Mx3.wExact P hP π
  unfold W1
  rw [mul_comm]
  exact this.symm
end Formalism.FourierDecayAlt.P.Mx6.WB
