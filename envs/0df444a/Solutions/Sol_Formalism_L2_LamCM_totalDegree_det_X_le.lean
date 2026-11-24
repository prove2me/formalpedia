-- Prove2me | solution 1 for Formalism.L2.LamCM.totalDegree_det_X_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:30.467793+00:00
-- url     : https://prove2.me/submissions/0393a324-d457-4d22-974d-b8975dfb2a52

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {k σ : Type} [Field k] (n : ℕ) (f : Fin n → Fin n → σ) :
    (Matrix.of fun i j => (X (f i j) : MvPolynomial σ k)).det.totalDegree ≤ n := by
  rw [Matrix.det_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
  rw [Units.smul_def]
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, ((Matrix.of fun i j => (X (f i j) : MvPolynomial σ k)) (s i) i).totalDegree
      ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by simp [totalDegree_X]
    _ = n := by simp
end Formalism.L2.LamCM
