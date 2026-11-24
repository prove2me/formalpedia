-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lgraded_coeff_euler
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:22.45852+00:00
-- url     : https://prove2.me/submissions/f04933f4-c689-4158-8081-41add4b83ea3

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_euler_monomial
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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv ℚ a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) * coeff m f := by
  induction f using MvPolynomial.induction_on'
  next m' c' =>
    rw [lgraded_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  next p q hp hq =>
    have hpq : rowDiv ℚ a a 1 (p + q) = rowDiv ℚ a a 1 p + rowDiv ℚ a a 1 q := by
      simp only [rowDiv, map_add, Polynomial.coeff_add]
    rw [hpq, coeff_add, coeff_add, hp, hq, mul_add]
end Formalism.GradedWeylDivisibility
