-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.normalisation_every_setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:43:29.470454+00:00
-- url     : https://prove2.me/submissions/36374f64-c036-414c-b6cb-56eb475a214a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.IntNormBFromNorm := fun h k r _ _ _ _ _ _ D =>
  h k r D.z D.z' D.μsec D.μG D.μW D.μN D.μW'
    ⟨D.k_pos, D.z_mem, D.z'_mem, D.T_pos, D.T'_pos, D.haarG, D.haarW, D.haarN, D.haarW', D.sec⟩
end Formalism.FourierDecayAlt.P
