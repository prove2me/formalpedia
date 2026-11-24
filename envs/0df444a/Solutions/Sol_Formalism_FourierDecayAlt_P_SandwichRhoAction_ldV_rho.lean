-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.ldV_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:28.793128+00:00
-- url     : https://prove2.me/submissions/2b750d9a-9095-4711-a904-f09d29202de8

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_deriv_comp_of_leftInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_sandw_leftInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_curveL

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (rho D p φ) g = rho D p (LdV (AdL p X) φ) g := by
  unfold LdV
  simp only [rho_eq, sgs_curveL D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0
end Formalism.FourierDecayAlt.P.SandwichRhoAction
