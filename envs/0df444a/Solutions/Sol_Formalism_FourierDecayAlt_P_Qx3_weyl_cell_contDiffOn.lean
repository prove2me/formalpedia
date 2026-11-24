-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.weyl_cell_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:56:25.885835+00:00
-- url     : https://prove2.me/submissions/94ddfd40-04e7-48d0-a505-f4f4be98656f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coordBar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cdo_matrix

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (l : Fin r) : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => w1 k r l (c l)) (OmX r) := by
  refine cdo_matrix fun p q => ?_
  unfold w1
  split_ifs
  · exact (cd_coord l).contDiffOn
  · exact (cd_coordBar l).contDiffOn.inv fun x hx => star_ne_zero.2 (hx l)
  · exact contDiffOn_const
  · exact contDiffOn_const
end Formalism.FourierDecayAlt.P.Qx3
