-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.unitaryInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:40.259914+00:00
-- url     : https://prove2.me/submissions/da5a0e9b-73b0-41e2-b1b2-b0608cfed00a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_muPi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_volume_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_measurable_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution : UnitaryInvariant := by
  intro d β W hW
  refine ⟨measurable_mulVec d W, ?_⟩
  rw [muPi_eq, Measure.map_smul, volume_unitary d W hW]
end Formalism.FourierDecayAlt.P.G8
