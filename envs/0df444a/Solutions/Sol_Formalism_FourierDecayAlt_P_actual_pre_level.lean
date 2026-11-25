-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.actual_pre_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:54.632932+00:00
-- url     : https://prove2.me/submissions/ae03b73d-3642-4a38-8f32-8aeba35f7774

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_APL_preOf_actual
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_place_alt_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.NF.ActualPreLevel := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl X
  exact ⟨Formalism.FourierDecayAlt.P.NFx1.APL.preOf X (Formalism.FourierDecayAlt.P.Qx5.place_alt_alt hpl), Formalism.FourierDecayAlt.P.NFx1.APL.preOf_actual X _⟩
end Formalism.FourierDecayAlt.P
