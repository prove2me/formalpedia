-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.mL_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:34.163423+00:00
-- url     : https://prove2.me/submissions/2194996a-c9a5-4bd9-bb85-e3b18bb65e02

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mfac_scale

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
theorem _root_.solution {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (g : ℝ) (hg : 0 < g) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L (g • σ) = crystallineComparison.mL K (fun v => L v / g) σ := by
  unfold crystallineComparison.mL
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hg, mfac_scale K _ g _ hg]
end Formalism.FourierDecayAlt.P.PBC.Lat
