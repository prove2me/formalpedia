-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_C_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:50.71566+00:00
-- url     : https://prove2.me/submissions/0a996584-e544-4a86-af39-5e84d25d8974

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Theorems.Thm_Formalism_REAL_fischerInner_monomial_left


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
theorem _root_.solution (a : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (C a) g = a * star (constantCoeff g) := by
  rw [C_apply, fischerInner_monomial_left, Finsupp.support_zero, Finset.prod_empty, Nat.cast_one, mul_one,
    constantCoeff_eq]
end Formalism.GradedWeylDivisibility
