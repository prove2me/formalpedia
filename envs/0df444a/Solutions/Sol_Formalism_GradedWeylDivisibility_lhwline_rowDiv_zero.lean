-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_rowDiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:18.157204+00:00
-- url     : https://prove2.me/submissions/39c751f0-5d68-4a52-8fbf-68a3c28a320b

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
theorem _root_.solution (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) K) :
    rowDiv K a b 0 g = g := by
  simp only [rowDiv]
  rw [← Polynomial.constantCoeff_apply]
  induction g using MvPolynomial.induction_on
  next c =>
    have h1 : rowGen K a b (C c : MvPolynomial (Fin r × Fin n) K) = Polynomial.C (C c) :=
      (rowGen (n := n) K a b).commutes c
    rw [h1, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp
end Formalism.GradedWeylDivisibility
