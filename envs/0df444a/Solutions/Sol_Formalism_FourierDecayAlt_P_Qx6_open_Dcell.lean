-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.open_Dcell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:21:04.775563+00:00
-- url     : https://prove2.me/submissions/d23639f8-7b00-4f53-a5dc-86563bac86d1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_open_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_open_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution {D : Set (Mx k r)} (hD : IsOpen D) (i : Fin (r + 1)) : IsOpen (UU (Dcell D i)) := by
  induction i using Fin.induction with
  | zero =>
    rw [Dcell_zero]
    exact open_const hD
  | succ l ih =>
    rw [Dcell_succ]
    exact open_step l ih
end Formalism.FourierDecayAlt.P.Qx6
