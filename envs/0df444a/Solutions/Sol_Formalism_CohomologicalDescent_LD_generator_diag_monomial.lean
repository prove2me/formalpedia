-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.generator_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:44.503864+00:00
-- url     : https://prove2.me/submissions/91edb750-9c96-458e-8ff3-c2d7128fadea

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_diag_variable
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_diag_constant
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a : Fin r) (m : Fin r × Fin r →₀ ℕ) (c : ℤ) :
    rowGen ℤ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, generator_diag_constant]
  simp_rw [map_pow, generator_diag_variable, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.weight_apply, Finsupp.sum, map_mul, map_prod]
  simp_rw [map_pow, smul_eq_mul, mul_comm (lgraded_wa a _)]
  ring
end Formalism.CohomologicalDescent.LD
