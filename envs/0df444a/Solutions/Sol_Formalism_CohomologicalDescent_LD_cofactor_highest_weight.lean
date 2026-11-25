-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_highest_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:46.966823+00:00
-- url     : https://prove2.me/submissions/92ea0032-b3cd-4184-b534-dfafa50ff025

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_top_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_sum
import Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_prod_leading_minors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_leading_minor_pow
import Theorems.Thm_Formalism_CohomologicalDescent_LD_telescoping_sum_eq_head
import Theorems.Thm_Formalism_CohomologicalDescent_LD_telescoping_weighted_sum

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
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) :
    genericDet ℤ r ^ (partialSumOfExponents ν 0) * cofMap r (hw ℤ le_rfl ν) = genericDet ℤ r ^ (∑ a, ν a) * ld3Q ν := by
  have h1 := telescoping_sum_eq_head (partialSumOfExponents ν) (partial_sequence_antitone ν hν) r
  have h2 := telescoping_weighted_sum (partialSumOfExponents ν) (partial_sequence_antitone ν hν) r
  rw [partial_sequence_top_eq_zero, add_zero] at h1
  rw [partial_sequence_top_eq_zero, mul_zero, add_zero, partial_sequence_sum] at h2
  rw [← h1, ← h2, highest_weight_prod_leading_minors, map_prod, ld3Q, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.mp hs
  rw [map_pow, ← mul_pow, cofactor_leading_minor_pow (show (s + 1) + (r - (s + 1)) = r by omega), mul_pow, ← pow_mul]
end Formalism.CohomologicalDescent.LD
