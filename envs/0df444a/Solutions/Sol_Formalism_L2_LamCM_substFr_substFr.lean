-- Prove2me | solution 1 for Formalism.L2.LamCM.substFr_substFr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:27.15016+00:00
-- url     : https://prove2.me/submissions/0c959b98-845c-4761-9d1b-4b11b6953091

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma

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
variable {B : Type} {m : B → ℕ}
namespace Formalism.L2.LamCM
theorem _root_.solution {R : Type} [CommRing R] (U U' : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) : substFr U (substFr U' P) = substFr (fun b => U b * U' b) P := by
  unfold substFr
  rw [bind₁_bind₁]
  refine congrArg (fun g => bind₁ g P) (funext fun v => ?_)
  simp only [map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.L2.LamCM
