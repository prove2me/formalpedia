-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.sign_insert_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:13.217962+00:00
-- url     : https://prove2.me/submissions/40d6ab4a-05f5-4b62-b09d-2867e6f7234b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_extend_perm

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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m p) = (-1) ^ (p.1 : ℕ) * Equiv.Perm.sign p.2 := by
  rw [phi0, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, sign_extend_perm]
end Formalism.FourierDecayAlt.P.Qx6
