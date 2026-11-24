-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_coeff_binForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:37.38092+00:00
-- url     : https://prove2.me/submissions/8aea7e75-079c-400c-9fb1-4727705bb2c4

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_xy_eq
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mono_inj
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binForm_apply

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] (d : ℕ) (c : Fin (d + 1) → R) (i : Fin (d + 1)) :
    coeff (la_mono (0 : Fin 1) (d - i.val) i.val) (binForm R d c) = c i := by
  rw [la_binForm_apply, coeff_sum, Finset.sum_eq_single i]
  · rw [coeff_smul, la_xy_eq, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [coeff_smul, la_xy_eq, coeff_monomial, if_neg, smul_zero]
    intro h
    exact hj (Fin.ext (la_mono_inj 0 h).2)
  · intro h
    exact absurd (Finset.mem_univ i) h
end Formalism.CohomologicalDescent.LA
