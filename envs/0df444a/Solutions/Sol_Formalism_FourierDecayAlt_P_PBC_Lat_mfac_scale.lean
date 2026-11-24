-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.mfac_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:10.975519+00:00
-- url     : https://prove2.me/submissions/aa0f5adc-39be-47ae-b173-ef88e61ab234

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat

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
theorem _root_.solution (K : ℕ) (L g a : ℝ) (hg : 0 < g) :
    crystallineComparison.mfac K L (g * a) = crystallineComparison.mfac K (L / g) a := by
  unfold crystallineComparison.mfac
  by_cases h : a = 0
  · simp [h]
  · rw [if_neg (mul_ne_zero hg.ne' h), if_neg h]
    congr 2
    field_simp
end Formalism.FourierDecayAlt.P.PBC.Lat
