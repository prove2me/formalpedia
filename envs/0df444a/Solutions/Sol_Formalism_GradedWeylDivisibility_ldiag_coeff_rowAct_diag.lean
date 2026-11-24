-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_coeff_rowAct_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:08.695798+00:00
-- url     : https://prove2.me/submissions/436f709e-44bb-4cc2-a82b-06f853698546

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_rowAct_diag_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_aeval_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (t : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowAct ℂ (Matrix.diagonal t) f) = coeff m f * ∏ a : Fin r, t a ^ rowDeg m a := by
  rw [ldiag_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on'
  next u c =>
    rw [ldiag_aeval_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · rw [zero_mul]
  next p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]
end Formalism.GradedWeylDivisibility
