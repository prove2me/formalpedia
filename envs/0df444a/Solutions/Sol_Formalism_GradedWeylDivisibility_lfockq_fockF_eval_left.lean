-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_fockF_eval_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:53.096735+00:00
-- url     : https://prove2.me/submissions/ea192947-f1a7-4c7e-a9da-e7701cfa36b4

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eval_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_left

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
private lemma fockF_add_left_lemma {σ : Type*} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  unfold fockF
  have key : ∀ h : MvPolynomial σ ℂ, ∀ s : Finset (σ →₀ ℕ), h.support ⊆ s →
      ∑ m ∈ h.support, h.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
        ∑ m ∈ s, h.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    intro h s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [MvPolynomial.notMem_support_iff.mp hm]
    simp
  rw [key (f + f') (f.support ∪ f'.support) MvPolynomial.support_add,
    key f (f.support ∪ f'.support) Finset.subset_union_left,
    key f' (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
private lemma fockF_sum_left_lemma_2 {σ ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ)
    (g : MvPolynomial σ ℂ) : fockF (∑ i ∈ s, h i) g = ∑ i ∈ s, fockF (h i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fockF_add_left_lemma, ih]
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hN : P.natDegree < N) (t : ℂ) (G : MvPolynomial σ ℂ) :
    fockF (Polynomial.eval (C t) P) G = ∑ i ∈ Finset.range N, t ^ i * fockF (P.coeff i) G := by
  rw [lfockq_eval_C P N hN t, fockF_sum_left_lemma_2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LFocks_C_mul_left]
end Formalism.GradedWeylDivisibility
