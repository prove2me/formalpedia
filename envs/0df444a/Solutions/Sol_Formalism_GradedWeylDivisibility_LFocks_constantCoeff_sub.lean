-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_constantCoeff_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:50.840283+00:00
-- url     : https://prove2.me/submissions/cf5f3023-cf24-426b-9e65-a6b9a162dce6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_C

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
variable {σ : Type*} [Fintype σ]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (U : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (sub U g) = constantCoeff g := by
  induction g using MvPolynomial.induction_on
  next a => rw [LFocks_sub_C]
  next p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, map_mul, LFocks_sub_X]
    simp
end Formalism.GradedWeylDivisibility
