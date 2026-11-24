-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.herm_bvec_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:56.033289+00:00
-- url     : https://prove2.me/submissions/89bbf0ae-22ac-4b2e-948b-09c8992737e1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_fvec_out

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {p : Fin (2 * r + k + 1)}
    (hp : ¬ inV k r i p) : herm (Hpk k r) (bvec p) (fvec k r z i) = 0 := by
  unfold herm dotProduct
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : inV k r i q
  · rw [show (Hpk k r *ᵥ bvec p) q = Hpk k r q p by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply], hpk_out hq hp, mul_zero]
  · rw [Pi.star_apply, fvec_out hz hq, star_zero, zero_mul]
end Formalism.FourierDecayAlt.P.Qx2
