-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.boundsIVal_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:04.622389+00:00
-- url     : https://prove2.me/submissions/81a74143-fe30-4ab6-940f-398517c11922

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BoundsIVal
import Theorems.Thm_Formalism_DivisionValues_reduction_lemma_first


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (hI : BoundsI) : BoundsIVal := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n' n D H' E I0 hH hE hHE hI0 hrange hK0H hpos P hP A Bd hA G dG hG hdG hdual hBd w e he
  obtain ⟨hlat, hdual'⟩ := hI K n' n H' E I0 hH hE hHE hI0 hrange A Bd hA G dG hG hdG hdual hBd
  have key := Formalism.DivisionValues.reduction_lemma_first K K0 hK0 v0 hv0 n D (I0ᴴ * H' * I0) hK0H hpos P hP _ hlat
    (G * dG) 1 (Nat.mul_pos hG hdG) hdual' w e he
  simpa only [Nat.cast_one, one_mul] using key
end Formalism.BranchingDeterminantCap
