-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_pderiv_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:50.837855+00:00
-- url     : https://prove2.me/submissions/f143c029-dcac-4165-9aa5-bacad940e4dc

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_X

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
variable [DecidableEq σ]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (V : Matrix σ σ ℂ) (i : σ) (g : MvPolynomial σ ℂ) :
    pderiv i (sub V g) = ∑ j, C (V j i) * sub V (pderiv j g) := by
  induction g using MvPolynomial.induction_on
  next a => simp
  next p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  next p k hp =>
    have hS : pderiv i (sub V (X k)) = C (V k i) := by
      rw [LFocks_sub_X, map_sum]
      simp [pderiv_X, Pi.single_apply]
    have hT : ∀ j, sub V (pderiv j (X k : MvPolynomial σ ℂ)) = if j = k then 1 else 0 := by
      intro j
      rw [pderiv_X]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [map_mul, pderiv_mul, hp, hS]
    simp only [pderiv_mul, map_add, map_mul, hT, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [mul_comm]
end Formalism.GradedWeylDivisibility
