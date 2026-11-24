-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lgraded_rowGen_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:10.76662+00:00
-- url     : https://prove2.me/submissions/e66ee2a3-4e46-420e-882b-3e2e3f214ee1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_rowGen_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_rowGen_C
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
theorem _root_.solution {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowGen ℚ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next => rw [monomial_zero', lgraded_rowGen_C]; simp
  next v k m _ _ ih =>
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v k) = k * lgraded_wa a v := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [add_comm, monomial_add_single, map_mul, ih, map_pow, lgraded_rowGen_X, map_add, map_mul,
      map_pow, hw, mul_pow, ← pow_mul, pow_add, mul_comm (lgraded_wa a v) k]
    ring
end Formalism.GradedWeylDivisibility
