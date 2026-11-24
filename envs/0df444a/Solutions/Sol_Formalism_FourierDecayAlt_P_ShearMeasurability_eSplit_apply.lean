-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.eSplit_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:26.659144+00:00
-- url     : https://prove2.me/submissions/a889d448-14d1-4e61-8b0e-d9577df08a6a

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {m : ℕ} (w : Equiv.Perm (Fin m))
namespace Formalism.FourierDecayAlt.P.ShearMeasurability
theorem _root_.solution (x : C2.Lidx m → ℂ) :
    eSplit w x = (fun a => x ⟨a.1, a.2.1⟩, fun b => x ⟨b.1, b.2.1⟩) := by rfl
end Formalism.FourierDecayAlt.P.ShearMeasurability
