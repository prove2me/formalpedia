-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:47.156539+00:00
-- url     : https://prove2.me/submissions/63a94745-36b0-4479-bdb6-628adee99a12

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_rw_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_lw_rho

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (u v : List (Mat k r))
    (f : Mat k r → (Wq →L[ℂ] Wp)) : dLR u v (rho D p f) = rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) f) := by
  show u.foldr LdV (Rw v (rho D p f)) = rho D p ((u.map (AdL p)).foldr LdV (Rw (v.map (AdR p)) f))
  rw [rw_rho D hp v f, lw_rho D hp u]
end Formalism.FourierDecayAlt.P.SandwichRhoAction
