-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_eval_colAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:56.837214+00:00
-- url     : https://prove2.me/submissions/fc99a864-2dbb-4e4e-accc-cf684e64205b

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type*} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (l j : Fin n) (c : K) (x : Fin r × Fin n → K)
    (g : MvPolynomial (Fin r × Fin n) K) :
    eval x (colAdd K l j c g) = eval (lhwline_colOp l j c x) g := by
  induction g using MvPolynomial.induction_on
  next c =>
    simp [colAdd]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp, colAdd, aeval_X, lhwline_colOp]
    congr 1
    split_ifs <;> simp [lhwline_colOp, *]
end Formalism.GradedWeylDivisibility
