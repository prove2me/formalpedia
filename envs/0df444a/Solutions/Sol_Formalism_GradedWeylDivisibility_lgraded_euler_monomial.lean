-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lgraded_euler_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:17.461821+00:00
-- url     : https://prove2.me/submissions/60e53f22-4e97-488b-a1c2-701cac2f2adf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_rowGen_monomial

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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowDiv ℚ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) • monomial m c := by
  rw [rowDiv, lgraded_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]
end Formalism.GradedWeylDivisibility
