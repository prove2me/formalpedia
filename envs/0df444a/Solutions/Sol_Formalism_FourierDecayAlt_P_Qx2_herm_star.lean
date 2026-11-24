-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.herm_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:35:06.348823+00:00
-- url     : https://prove2.me/submissions/a9861b52-e08a-498d-851f-07abdf211892

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_h
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

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
theorem _root_.solution (v w : Fin (2 * r + k + 1) → ℂ) : star (herm (Hpk k r) v w) = herm (Hpk k r) w v := by
  have hH : ∀ a b, star (Hpk k r a b) = Hpk k r b a := fun a b => by
    have h := congrFun (congrFun (hpk_h (k := k) (r := r)) b) a
    rw [Matrix.conjTranspose_apply] at h
    exact h
  simp only [herm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star,
    Finset.mul_sum, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end Formalism.FourierDecayAlt.P.Qx2
