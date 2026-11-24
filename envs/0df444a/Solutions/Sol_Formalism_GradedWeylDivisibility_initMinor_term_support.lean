-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.initMinor_term_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:43.960858+00:00
-- url     : https://prove2.me/submissions/fdebbbc2-57d1-4041-8ec1-76e0b43587e4

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_support_prod_eq_of_additive
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_single
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_single
import Theorems.Thm_P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ (∏ i : Fin s, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)).support) :
    (∀ k, rowPart k m = #{p : Fin s | (I p).val < k}) ∧ rowTot m = s := by
  classical
  constructor
  · intro k
    have h := support_prod_eq_of_additive (rowPart k) (rowPart_zero k) (rowPart_add k) Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun i => if (I (σ i)).val < k then 1 else 0)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowPart_single k _ _) m hm
    rw [h, Equiv.sum_comp σ (fun p => if (I p).val < k then 1 else 0), Finset.sum_boole]
    simp
  · have h := support_prod_eq_of_additive rowTot rowTot_zero rowTot_add Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun _ => 1)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowTot_single _ _) m hm
    rw [h]; simp
end Formalism.GradedWeylDivisibility
