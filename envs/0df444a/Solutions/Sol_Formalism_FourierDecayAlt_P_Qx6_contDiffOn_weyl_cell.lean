-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:59:16.779124+00:00
-- url     : https://prove2.me/submissions/9a02ff3f-0336-4900-9592-8ec45e71516e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_cd_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coordBar


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (l : Fin r) : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => w1 k r l (c l)) (OmX r) := by
  rw [cd_entries]
  intro p q
  unfold w1
  split_ifs
  · exact (Qx3.cd_coord l).contDiffOn
  · exact (Qx3.cd_coordBar l).contDiffOn.inv (fun x hx => star_ne_zero.2 (hx l))
  · exact contDiffOn_const
  · exact contDiffOn_const
end Formalism.FourierDecayAlt.P.Qx6
