-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.exp_eq_one_iff_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:19.463866+00:00
-- url     : https://prove2.me/submissions/4a9f55d2-a6da-4285-8f06-a9427a4a0ac1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Bl_general_b_fact_right_side_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.PBC.Lat
namespace Formalism.FourierDecayAlt.P.PBC.Lat
theorem _root_.solution (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ n : ℤ, x = n := by
  first | exact Bl.general_b_fact_right_side.goal1 .. | (apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_side.goal1 x
end Formalism.FourierDecayAlt.P.PBC.Lat
