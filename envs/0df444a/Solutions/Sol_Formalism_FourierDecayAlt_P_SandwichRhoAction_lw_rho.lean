-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.lw_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:22.910893+00:00
-- url     : https://prove2.me/submissions/5e709c6d-e49f-4a2a-b2a5-ce3edb9aab64

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_ldV_rho

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
    ∀ (u : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)),
      u.foldr LdV (rho D p φ) = rho D p ((u.map (AdL p)).foldr LdV φ)
  | [], _ => rfl
  | X :: u, φ => by
    funext g
    show LdV X (u.foldr LdV (rho D p φ)) g = rho D p (LdV (AdL p X) ((u.map (AdL p)).foldr LdV φ)) g
    rw [solution D hp u φ, ldV_rho D hp]
end Formalism.FourierDecayAlt.P.SandwichRhoAction
