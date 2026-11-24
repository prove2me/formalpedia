-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.eSplit_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:27.987737+00:00
-- url     : https://prove2.me/submissions/6a52677c-f4d2-41a7-9728-19a9981b72f2

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
theorem _root_.solution : MeasurePreserving (eSplit w) volume volume :=
  (measurePreserving_sumPiEquivProdPi (fun _ => (volume : Measure ℂ))).comp
    ((measurePreserving_piCongrLeft (fun _ => (volume : Measure ℂ)) (splitEquiv w).symm).symm _)
end Formalism.FourierDecayAlt.P.ShearMeasurability
