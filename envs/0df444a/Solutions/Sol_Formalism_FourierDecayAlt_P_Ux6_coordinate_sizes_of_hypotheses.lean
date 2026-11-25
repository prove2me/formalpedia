-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:29.78401+00:00
-- url     : https://prove2.me/submissions/13bfa3fe-eefe-44c2-85ba-5b7d96904d5a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_detZj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_coordinate_sizes_of_parts_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (hSM : SliceMem) (hU1 : BigCellCoordinateSizes) (hU2 : BlockHeadSizes) (hZh : ZhSlice) : SliceCoordinateSizes :=
  coordinate_sizes_of_parts_holds hSM hU1 hU2 hZh detZj
end Formalism.FourierDecayAlt.P.Ux6
