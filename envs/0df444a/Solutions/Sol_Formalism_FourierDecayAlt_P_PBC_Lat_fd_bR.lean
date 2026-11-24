-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.fd_bR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:14.776993+00:00
-- url     : https://prove2.me/submissions/320c9303-fe1d-45c9-966e-b39629f0d36d

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
theorem _root_.solution (f : ℕ) (R : ℝ) (hR : 0 < R) :
    ZSpan.fundamentalDomain (bR f R hR) = R • ZSpan.fundamentalDomain (b0 f) := by
  ext m
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  simp only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, bR, Module.Basis.repr_isUnitSMul, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  constructor <;> intro h i <;> simpa [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec] using h i
end Formalism.FourierDecayAlt.P.PBC.Lat
