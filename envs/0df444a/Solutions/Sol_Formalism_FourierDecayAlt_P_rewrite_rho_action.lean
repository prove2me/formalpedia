-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rewrite_rho_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:51.326032+00:00
-- url     : https://prove2.me/submissions/dde00b49-782f-499a-bcaf-9c7225e14ee3

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_dLR_rho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SandwichRhoAction
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : RwRho := by
  intro k r Wp Wq _ _ _ _ D m f p hp _ u v _ _ _ g _
  exact congrFun (dLR_rho D hp u v f) g
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.SandwichRhoAction
