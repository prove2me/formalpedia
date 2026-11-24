-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:20.657942+00:00
-- url     : https://prove2.me/submissions/fe0d3af7-6851-4787-9b1a-20ff3f61f8e7

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_dmin_sgs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution (Bs : RealPlaceData k r Wp Wq) {p : SS k r} (hp : Bs.inSS p) (g : Mat k r) :
    Gf k r Bs.z Bs.z' (sgs p g) = Gf k r Bs.z Bs.z' g := by
  unfold Formalism.QuantumDeterminants.Gf
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]
end Formalism.FourierDecayAlt.P.JCx1.needs
