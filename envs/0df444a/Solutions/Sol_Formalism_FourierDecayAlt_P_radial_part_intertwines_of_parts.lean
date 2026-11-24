-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.radial_part_intertwines_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:04.172638+00:00
-- url     : https://prove2.me/submissions/2ca8b314-b964-4a3d-a45e-ccabc08dbc0f

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.RadialPartIntertwinesFromComponents := by
  intro hJ hG k r Wp Wq _ _ _ _ _ _ D A m F Θ ho hT hF hC
  filter_upwards [hG k r Wp Wq D] with q hq
  exact (hJ k r Wp Wq D A m F Θ ho hT hF hC _ hq).symm
end Formalism.FourierDecayAlt.P
