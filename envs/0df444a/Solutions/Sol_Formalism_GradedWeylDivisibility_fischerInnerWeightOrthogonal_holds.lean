-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerWeightOrthogonal_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:14.170811+00:00
-- url     : https://prove2.me/submissions/0279c7a3-b16d-46ee-9974-2065ae8f289e

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockWeightOrth

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
theorem _root_.solution : FockWeightOrth := by
  intro σ M _ w μ μ' f g hne hf hg
  unfold Formalism.REAL.fockF
  refine Finset.sum_eq_zero fun m hm => ?_
  have hgm : g.coeff m = 0 := by
    by_contra h
    exact hne ((hf (mem_support_iff.mp hm)).symm.trans (hg h))
  rw [hgm, star_zero, mul_zero, zero_mul]
end Formalism.GradedWeylDivisibility
