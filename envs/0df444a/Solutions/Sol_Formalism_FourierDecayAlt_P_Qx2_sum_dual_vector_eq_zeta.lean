-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.sum_dual_vector_eq_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:24:57.845049+00:00
-- url     : https://prove2.me/submissions/03553783-2a68-41f4-bead-edbce7ca7552

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_fvec_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_posL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_expand

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
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (g : Mx k r) :
    ∑ j, ybv k r z i g j * xv k r z' i j = zetaL k r z z' i g := by
  unfold zetaL
  rw [herm_expand, ← sum_posL]
  · rfl
  · intro p hp
    rw [fvec_out hz' hp, mul_zero]
end Formalism.FourierDecayAlt.P.Qx2
