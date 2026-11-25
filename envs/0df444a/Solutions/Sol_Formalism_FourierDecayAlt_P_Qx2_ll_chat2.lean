-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.ll_chat2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:49:49.936615+00:00
-- url     : https://prove2.me/submissions/eefd02c8-0e59-4c81-8c52-ba2dcaf6e214

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_ite
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
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) :
    LL k r i D (fun f : Mx k r → E => chat2L (EH k r) (posL k r i) u a a' β β' f) := ll_sum Finset.univ _ fun p _ => ll_sum Finset.univ _ fun p' _ => ll_sum Finset.univ _ fun q _ =>
    ll_sum Finset.univ _ fun q' _ =>
      LL.ite (LL.coef (Good.ll (good_qminor hD (skip2 p p') (skip2 q q') u))
        (fun g => (-1 : ℂ) ^ ((p : ℕ) + (p' : ℕ) + (q : ℕ) + (q' : ℕ)) * (β g p * β' g p' - β g p' * β' g p) *
          (a g q * a' g q' - a g q' * a' g q))) (p < p' ∧ q < q')
end Formalism.FourierDecayAlt.P.Qx2
