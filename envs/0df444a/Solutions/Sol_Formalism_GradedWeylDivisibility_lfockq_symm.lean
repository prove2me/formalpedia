-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:52.161464+00:00
-- url     : https://prove2.me/submissions/71f2a351-38ba-4340-ad78-d5780b468760

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eq_sum

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
variable {σ : Type*}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  classical
  rw [lfockq_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    lfockq_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)
end Formalism.GradedWeylDivisibility
