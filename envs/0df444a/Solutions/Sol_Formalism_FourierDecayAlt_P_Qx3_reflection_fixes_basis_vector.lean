-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:24:44.726411+00:00
-- url     : https://prove2.me/submissions/be411954-e95c-4513-b916-aa520bf3a93c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_o
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_dd_o
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_w1_apply

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
theorem _root_.solution (l : Fin r) (c : ℂ) {q : Fin (2 * r + k + 1)} (h1 : q ≠ eI k r l) (h2 : q ≠ esI k r l) :
    w1 k r l c *ᵥ bvec q = bvec q := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  rw [w1_apply, sw_o l h1 h2, dd_o l c h1 h2]
end Formalism.FourierDecayAlt.P.Qx3
