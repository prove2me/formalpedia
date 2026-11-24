-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.rw_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:45.929808+00:00
-- url     : https://prove2.me/submissions/74a21998-2eb6-43cd-83c6-312c682cb333

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_rdV_rho

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (v : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)), Rw v (rho D p φ) = rho D p (Rw (v.map (AdR p)) φ)
  | [], _ => rfl
  | X :: v, φ => by
    funext g
    show RdV X (Rw v (rho D p φ)) g = rho D p (RdV (AdR p X) (Rw (v.map (AdR p)) φ)) g
    rw [solution D hp v φ, rdV_rho D hp]
end Formalism.FourierDecayAlt.P.SandwichRhoAction
