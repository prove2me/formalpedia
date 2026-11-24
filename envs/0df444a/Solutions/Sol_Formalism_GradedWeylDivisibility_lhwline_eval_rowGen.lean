-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_eval_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:57.150135+00:00
-- url     : https://prove2.me/submissions/51d9456d-223d-4ad3-836b-2c40d672daa5

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
theorem _root_.solution (a b : Fin r) (t : K) (x : Fin r × Fin n → K)
    (g : MvPolynomial (Fin r × Fin n) K) :
    Polynomial.eval₂ (eval x) t (rowGen K a b g) = eval (lhwline_rowOp a b t x) g := by
  induction g using MvPolynomial.induction_on
  next c =>
    have h1 : rowGen K a b (C c : MvPolynomial (Fin r × Fin n) K) = Polynomial.C (C c) :=
      (rowGen (n := n) K a b).commutes c
    rw [h1, Polynomial.eval₂_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
  next p q hp hq =>
    simp only [map_add, Polynomial.eval₂_add, hp, hq]
  next p v hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, map_mul]
    congr 1
    simp only [rowGen, aeval_X, eval_X, lhwline_rowOp]
    split_ifs <;> simp <;> ring
end Formalism.GradedWeylDivisibility
