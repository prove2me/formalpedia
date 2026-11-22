-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_C_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:07.654367+00:00
-- url     : https://prove2.me/submissions/2ca3379e-9b35-4c15-9e59-b3657e97eb42

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
    fockF f (C c * g) = star c * fockF f g := by
  simp only [fockF, coeff_C_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring
end Formalism.GradedWeylDivisibility
