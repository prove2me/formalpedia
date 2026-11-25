-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.comm_RZ_LZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:45.387453+00:00
-- url     : https://prove2.me/submissions/f2880c00-d877-4fb2-8801-a24c4059974a

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_good_ld
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_Comm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_Comm_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_good_LZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_comm_rd_ld
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_rd


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
    (h2' : inLieLev k r i (hpart2 (Hpk k r) Z')) :
    Comm (E := E) k r i D (RZ (Hpk k r) Z') (LZ (Hpk k r) Z) := by
  have hR : ∀ Y, inLieLev k r i Y → Comm (E := E) k r i D (LZ (Hpk k r) Z) (fun f => RdV Y f) := fun Y hY =>
    Comm.lin (Qx2.good_rd hD hY) (good_ld hD h1) (good_ld hD h2) (comm_rd_ld h1 hY).symm
      (comm_rd_ld h2 hY).symm Complex.I
  exact Comm.lin (good_LZ hD h1 h2) (Qx2.good_rd hD h1') (Qx2.good_rd hD h2') (hR _ h1').symm (hR _ h2').symm
    Complex.I
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
