-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_fockF_eval_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:53.65047+00:00
-- url     : https://prove2.me/submissions/ec5ad48b-5e9c-4def-ac8e-d510a6d71aad

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eval_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Formalism.REAL
noncomputable section
namespace Formalism.GradedWeylDivisibility
private lemma fockF_add_right_lemma_3 {σ : Type*} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring
private lemma fockF_sum_right_lemma_4 {σ ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ)
    (f : MvPolynomial σ ℂ) : fockF f (∑ i ∈ s, h i) = ∑ i ∈ s, fockF f (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fockF_add_right_lemma_3, ih]
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hN : P.natDegree < N) (t : ℂ) (F : MvPolynomial σ ℂ) :
    fockF F (Polynomial.eval (C t) P) = ∑ i ∈ Finset.range N, star (t ^ i) * fockF F (P.coeff i) := by
  rw [lfockq_eval_C P N hN t, fockF_sum_right_lemma_4]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LFocks_C_mul_right]
end Formalism.GradedWeylDivisibility
