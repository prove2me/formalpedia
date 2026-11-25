-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.comm_lop_rop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:25.386574+00:00
-- url     : https://prove2.me/submissions/72e72954-f320-443b-a32e-f021a3323e5b

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_Comm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_comm_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_Comm_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_good_RZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_good_LZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_good_rop
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_comm_RZ_LZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_id


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution (hD : IsOpen D) {Z Z' : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (h1' : inLieLev k r i (hpart1 (Hpk k r) Z'))
    (h2' : inLieLev k r i (hpart2 (Hpk k r) Z')) (c c' : ℂ) :
    Comm (E := E) k r i D (lop k r c Z) (rop k r c' Z') := by
  have h := Comm.lin (E := E) (good_LZ hD h1 h2) (good_RZ hD h1' h2') Qx2.good_id (comm_RZ_LZ hD h1 h2 h1' h2')
    (comm_id _) c'
  exact Comm.lin (good_rop hD h1' h2' c') (good_LZ hD h1 h2) Qx2.good_id h.symm (comm_id _) c
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
