-- Prove2me | solution 1 for Formalism.REAL.fischerInner_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:24.458949+00:00
-- url     : https://prove2.me/submissions/d1eda902-f7e6-4d4f-b2be-a0185ebffe1a

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle

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
open Formalism Formalism.REAL
variable {σ : Type*}
namespace Formalism.REAL
theorem _root_.solution (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by
  classical
  rw [fischerInner_eq_sum_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset g f (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]; ring
end Formalism.REAL
