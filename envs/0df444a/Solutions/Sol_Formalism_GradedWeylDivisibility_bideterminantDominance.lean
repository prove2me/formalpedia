-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.bideterminantDominance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:28.169805+00:00
-- url     : https://prove2.me/submissions/6480758f-c928-477a-8f43-90c588ee508a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_support
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_min_eq_shapeDeg
import Theorems.Thm_Formalism_GradedWeylDivisibility_support_prod_eq_of_additive
import Theorems.Thm_Formalism_GradedWeylDivisibility_support_prod_le_of_additive


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
theorem _root_.solution : BideterminantDominance := by
  classical
  intro R _ r n K sz hsz I m hm
  have hm' : m ∈ (∏ k : Fin K, initMinor R (I k) (hsz k)).support := hm
  refine ⟨fun k => ?_, ?_⟩
  · have h := support_prod_le_of_additive (rowPart k) (rowPart_zero k)
      (rowPart_add k) Finset.univ (fun k' => initMinor R (I k') (hsz k'))
      (fun k' => min k (sz k'))
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').1 k)
      m hm'
    exact h.trans_eq (sum_min_eq_shapeDeg sz hsz k)
  · have h := support_prod_eq_of_additive rowTot rowTot_zero
      rowTot_add Finset.univ (fun k' => initMinor R (I k') (hsz k')) sz
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').2)
      m hm'
    have h2 := sum_min_eq_shapeDeg sz hsz n
    have h3 : ∑ t : Fin n with t.val < n, shapeDeg sz t =
        ∑ t : Fin n, shapeDeg sz t :=
      Finset.sum_congr (Finset.filter_true_of_mem fun t _ => t.isLt) fun _ _ => rfl
    have h4 : ∑ k' : Fin K, min n (sz k') = ∑ k' : Fin K, sz k' :=
      Finset.sum_congr rfl fun k' _ => min_eq_right (hsz k')
    exact h.trans (h4.symm.trans (h2.trans h3))
end Formalism.GradedWeylDivisibility
