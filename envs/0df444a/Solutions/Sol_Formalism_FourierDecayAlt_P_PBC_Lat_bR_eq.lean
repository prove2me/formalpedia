-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.bR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:51:53.034811+00:00
-- url     : https://prove2.me/submissions/9fc383ad-6896-4e50-b4c0-069f0a739c50

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_standard_lattice_basis_apply

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
theorem _root_.solution (f : ℕ) (R : ℝ) (hR : 0 < R) : ⇑(bR f R hR) = gen f R := by
  funext p
  obtain ⟨v, β⟩ := p
  rw [bR, Module.Basis.isUnitSMul_apply, standard_lattice_basis_apply, gen]
  cases β <;> funext u <;> by_cases h : u = v <;> simp_all [Complex.real_smul]
end Formalism.FourierDecayAlt.P.PBC.Lat
