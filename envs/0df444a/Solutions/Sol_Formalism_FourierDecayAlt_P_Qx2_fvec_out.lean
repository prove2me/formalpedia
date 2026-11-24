-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.fvec_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:37.41382+00:00
-- url     : https://prove2.me/submissions/3b337e35-ce9b-4224-a7f7-beb9bb140d1c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {p : Fin (2 * r + k + 1)}
    (hp : ¬ inV k r i p) : fvec k r z i p = 0 := by
  unfold fvec
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro e
    apply hp
    rw [e]
    show i.val ≤ i.val ∧ i.val + i.val ≤ 2 * r + k
    omega
  · apply hz
    unfold inV at hp
    have := i.isLt
    omega
end Formalism.FourierDecayAlt.P.Qx2
