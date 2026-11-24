-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dominancePowerProduct_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:00.024174+00:00
-- url     : https://prove2.me/submissions/1a9d2db3-83f0-489d-b685-11a70d6157c2

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_domPow_nat
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_sum_filter_lt_eq_range
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_sum_univ_eq_range
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_prod_univ_eq_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : DomPow := by
  intro r t μ lam ht0 ht hS hT
  rw [ldiag_prod_univ_eq_range, ldiag_prod_univ_eq_range]
  have hext0 : ∀ a, 0 ≤ ldiagExt t a := fun a => by
    unfold ldiagExt; split_ifs
    · exact ht0 _
    · exact le_rfl
  refine ldiag_domPow_nat (ldiagExt t) hext0 ?_ (ldiagExt μ) (ldiagExt lam) r ?_ ?_
  · intro a b hab
    by_cases hb : b < r
    · have ha : a < r := lt_of_le_of_lt hab hb
      simp only [ldiagExt, dif_pos ha, dif_pos hb]
      exact ht (show (⟨a, ha⟩ : Fin r) ≤ ⟨b, hb⟩ from hab)
    · simp only [ldiagExt, dif_neg hb]
      exact hext0 a
  · intro k hk
    rw [← ldiag_sum_filter_lt_eq_range μ k hk, ← ldiag_sum_filter_lt_eq_range lam k hk]
    exact hS k
  · rw [← ldiag_sum_univ_eq_range, ← ldiag_sum_univ_eq_range]
    exact hT
end Formalism.GradedWeylDivisibility
