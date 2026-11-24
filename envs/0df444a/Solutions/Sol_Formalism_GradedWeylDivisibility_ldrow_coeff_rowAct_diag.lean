-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:17.022425+00:00
-- url     : https://prove2.me/submissions/65589717-9a27-41c9-9307-23d0eb772613

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_rowAct_diag_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_aeval_monomial
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
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (f : MvPolynomial (Fin k × Fin n) R) (m : Fin k × Fin n →₀ ℕ) :
    coeff m (rowAct R (Matrix.diagonal t) f) = coeff m f * ∏ a : Fin k, t a ^ rowDeg m a := by
  rw [ldrow_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [ldrow_aeval_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]
end Formalism.GradedWeylDivisibility
