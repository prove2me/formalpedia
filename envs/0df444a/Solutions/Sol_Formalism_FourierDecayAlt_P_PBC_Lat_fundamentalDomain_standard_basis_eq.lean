-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.fundamentalDomain_standard_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:11.942524+00:00
-- url     : https://prove2.me/submissions/031e8856-1b64-4831-b928-eec16d6601d5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_standard_lattice_basis_repr

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
theorem _root_.solution (f : ℕ) : ZSpan.fundamentalDomain (b0 f) =
    Set.pi Set.univ (fun _ : Fin f => {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1}) := by
  ext m
  simp only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall,
    standard_lattice_basis_repr, Bool.forall_bool, if_false, if_true, Bool.false_eq_true]
end Formalism.FourierDecayAlt.P.PBC.Lat
