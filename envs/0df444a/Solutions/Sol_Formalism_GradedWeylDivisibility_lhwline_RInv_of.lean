-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_RInv_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:11.862918+00:00
-- url     : https://prove2.me/submissions/ff7c5795-e3fb-4484-b437-6486e28264d9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_eval_rowGen

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
variable {K : Type*} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (g : MvPolynomial (Fin r × Fin n) K)
    (h : ∀ a b : Fin r, a < b → rowGen K a b g = Polynomial.C g) :
    lhwline_RInv (fun x => eval x g) := by
  intro x a b t hab
  show eval (lhwline_rowOp a b t x) g = eval x g
  rw [← lhwline_eval_rowGen, h a b hab, Polynomial.eval₂_C]
end Formalism.GradedWeylDivisibility
