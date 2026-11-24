-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_pderiv_none_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:01.3669+00:00
-- url     : https://prove2.me/submissions/8a860ce7-8efc-4303-9a1c-a74d11af0f32

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p v hp => simp [Derivation.leibniz, hp, pderiv_X]
end Formalism.GradedWeylDivisibility
