-- Prove2me | solution 1 for Formalism.L2.LamCM.evalFr_substFr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:46.032815+00:00
-- url     : https://prove2.me/submissions/3a04f800-34d8-4653-9f65-1b75e900faf2

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
theorem _root_.solution {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    evalFr (substFr U P) Y = evalFr P (fun b => (U b).transpose * Y b) := by
  unfold evalFr substFr
  show eval₂Hom (RingHom.id R) _ (bind₁ _ P) = eval₂Hom (RingHom.id R) _ P
  rw [eval₂Hom_bind₁]
  refine congrArg (fun g => eval₂Hom (RingHom.id R) g P) (funext fun v => ?_)
  simp [Matrix.mul_apply, mul_comm]
end Formalism.L2.LamCM
