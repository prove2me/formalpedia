-- Prove2me | solution 1 for Formalism.L2.LamCM.map_substFr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:28.894817+00:00
-- url     : https://prove2.me/submissions/ac83405f-6806-4948-bc91-1ca1d27edab8

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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) :
    MvPolynomial.map f (substFr U P) = substFr (fun b => (U b).map f) (MvPolynomial.map f P) := by
  unfold substFr
  rw [map_bind₁]
  refine congrArg (fun g => bind₁ g (MvPolynomial.map f P)) (funext fun v => ?_)
  simp [map_sum, map_mul, map_C, map_X]
end Formalism.L2.LamCM
