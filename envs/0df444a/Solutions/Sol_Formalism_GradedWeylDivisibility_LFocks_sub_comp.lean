-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_sub_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:50.864155+00:00
-- url     : https://prove2.me/submissions/41212d04-f4c0-4b86-8e8c-cf6d12e9a90b

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
theorem _root_.solution (A B : Matrix σ σ ℂ) :
    (sub A).comp (sub B) = sub (B * A) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, LFocks_sub_X, LFocks_sub_X, map_sum]
  simp only [map_mul, LFocks_sub_C, LFocks_sub_X, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
end Formalism.GradedWeylDivisibility
