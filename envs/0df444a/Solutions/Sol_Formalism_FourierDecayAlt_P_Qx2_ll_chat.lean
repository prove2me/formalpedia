-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.ll_chat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:35.766551+00:00
-- url     : https://prove2.me/submissions/c243263c-baef-45bc-a81c-3864f7c2bb0d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_sum

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
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) :
    LL k r i D (fun f : Mx k r → E => chatL (EH k r) (posL k r i) u a β f) := ll_sum Finset.univ _ (fun p _ => ll_sum Finset.univ _ (fun q _ =>
    LL.coef (Good.ll (good_qminor hD (skip1 p) (skip1 q) u))
      (fun g => (-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β g p * a g q)))
end Formalism.FourierDecayAlt.P.Qx2
