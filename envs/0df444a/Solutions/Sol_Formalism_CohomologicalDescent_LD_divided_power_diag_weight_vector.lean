-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_diag_weight_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:46.112422+00:00
-- url     : https://prove2.me/submissions/c16eedfa-fb79-4d16-a5f9-4ca7a6f71bb6

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_diag_monomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_weight_rowW
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a : Fin r) (k : ℕ) (μ : Fin r → ℕ) (y : MvPolynomial (Fin r × Fin r) ℤ)
    (hy : IsWeightedHomogeneous (rowW r r) y μ) : rowDiv ℤ a a k y = ((μ a).choose k : ℤ) • y := by
  have h1 : rowDivL ℤ a a k y = ((μ a).choose k : ℤ) • y := by
    conv_lhs => rw [y.as_sum]
    conv_rhs => rw [y.as_sum]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [rowDivL_apply, rowDiv, generator_diag_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
      ← lgraded_weight_rowW, hy (mem_support_iff.mp hd), smul_eq_C_mul, mul_comm]
    simp
  exact h1
end Formalism.CohomologicalDescent.LD
