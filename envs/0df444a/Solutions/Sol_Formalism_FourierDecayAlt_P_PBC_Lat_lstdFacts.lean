-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.lstdFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:08:31.864145+00:00
-- url     : https://prove2.me/submissions/5be7b14a-f05d-4212-ac8a-79e9da2a9de0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_lstd_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mem_dual_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_bR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_volume_fundamentalDomain_standard_basis
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_fd_bR
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_finrank_V

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
theorem _root_.solution : PBC.LstdFacts := by
  intro f R hR
  rw [lstd_eq, ← bR_eq f R hR]
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (bR f R hR) volume),
      fd_bR, Measure.real, Measure.addHaar_smul, volume_fundamentalDomain_standard_basis, finrank_V]
    simp [abs_of_pos hR, hR.le]
  · intro σ
    rw [bR_eq, ← lstd_eq]
    exact mem_dual_iff f R hR σ
end Formalism.FourierDecayAlt.P.PBC.Lat
