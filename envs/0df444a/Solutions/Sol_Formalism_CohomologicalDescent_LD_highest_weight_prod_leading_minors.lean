-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.highest_weight_prod_leading_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:38.630537+00:00
-- url     : https://prove2.me/submissions/f7964214-71d7-4085-a92d-da07d85ba02c

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_val

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
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) :
    hw ℤ le_rfl ν = ∏ s ∈ Finset.range r, leadingMinorPolynomial r (s + 1) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun s => leadingMinorPolynomial r (s + 1) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1)))]
  unfold hw
  refine Finset.prod_congr rfl fun s _ => ?_
  have h1 : leadingMinorPolynomial r (s.val + 1) = lpMinor ℤ (s.val + 1) (by omega) (by omega) := dif_pos (by omega)
  have h2 : nuNext ν s = partialSumOfExponents ν (s.val + 1) := rfl
  rw [h1, h2, partial_sequence_val]
end Formalism.CohomologicalDescent.LD
