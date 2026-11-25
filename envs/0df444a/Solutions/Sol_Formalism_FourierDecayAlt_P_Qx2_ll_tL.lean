-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.ll_tL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:22.436059+00:00
-- url     : https://prove2.me/submissions/dda779c6-916c-45c0-99f2-30c0f5a79071

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_chat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_chat2

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    LL k r i D (fun f : Mx k r → E => tL k r z z' i Y p q f) := by
  match p, q with
  | 0, 0 => exact Good.ll (good_qminor hD id id (uC k r i Y))
  | 0, 1 => exact LL.neg (ll_chat hD _ _ _)
  | 1, 0 => exact LL.neg (ll_chat hD _ _ _)
  | 1, 1 => exact LL.neg (ll_chat2 hD _ _ _ _ _)
end Formalism.FourierDecayAlt.P.Qx2
