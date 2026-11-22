-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_C_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:05.840574+00:00
-- url     : https://prove2.me/submissions/6558e1df-ad14-4a54-866f-eb30c586339c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {σ : Type*}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (C c * f) g = c * fockF f g := by
  rw [C_mul', fischerInner_eq_sum_of_subset (c • f) g f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring
end Formalism.GradedWeylDivisibility
