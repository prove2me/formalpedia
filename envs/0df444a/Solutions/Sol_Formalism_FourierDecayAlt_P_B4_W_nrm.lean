-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.W_nrm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:22:44.527503+00:00
-- url     : https://prove2.me/submissions/b0eb9f01-0966-4dcd-95c1-776201baed29

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_letter_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_nrm_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (w : List (Bool × Mat k r)) (F : Mat k r → E) : W w F = pn w • W (w.map nrm) F := by
  induction w with
  | nil => simp [pn, W]
  | cons x w ih =>
    rw [W_cons, ih, List.map_cons, W_cons, pn_cons, op_rsmul]
    conv_lhs => rw [nrm_smul x.2]
    rw [op_letter_smul, smul_smul, mul_comm (pn w)]
    rfl
end Formalism.FourierDecayAlt.P.B4
