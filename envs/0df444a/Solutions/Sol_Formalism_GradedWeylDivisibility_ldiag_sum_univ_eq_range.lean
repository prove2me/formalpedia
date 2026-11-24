-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_sum_univ_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:09.047991+00:00
-- url     : https://prove2.me/submissions/e9eceaee-92aa-41e3-90db-8e360d9c11d6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_sum_filter_lt_eq_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r : ℕ} (f : Fin r → ℕ) :
    ∑ a : Fin r, f a = ∑ a ∈ range r, ldiagExt f a := by
  have h := ldiag_sum_filter_lt_eq_range f r le_rfl
  simpa using h
end Formalism.GradedWeylDivisibility
