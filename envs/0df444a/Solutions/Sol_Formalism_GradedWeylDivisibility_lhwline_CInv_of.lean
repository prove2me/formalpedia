-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_CInv_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:48.044281+00:00
-- url     : https://prove2.me/submissions/54e03ee8-c964-49eb-bb92-f515ee2ac273

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_eval_colAdd

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
    (h : ∀ l j : Fin n, l < j → ∀ c : K, colAdd K l j c g = g) :
    lhwline_CInv (fun x => eval x g) := by
  intro x l j c hlj
  show eval (lhwline_colOp l j c x) g = eval x g
  rw [← lhwline_eval_colAdd, h l j hlj c]
end Formalism.GradedWeylDivisibility
