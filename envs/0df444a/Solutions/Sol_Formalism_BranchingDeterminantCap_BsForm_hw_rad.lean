-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.BsForm.hw_rad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:36.4228+00:00
-- url     : https://prove2.me/submissions/7f821ced-b356-47b5-8907-a30d56826623

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_hwspace
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_sumr
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_hw_weight
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowGraded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}
namespace Formalism.BranchingDeterminantCap.BsForm
theorem _root_.solution (H : BsForm sg D) (hsg : Antitone sg) (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg) : D (hw ℂ le_rfl sg) q = 0 := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW n n) q
  have hsum := sum_weightedHomogeneousComponent (rowW n n) q
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, H.sumr]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have hmem := dualWeylRowGraded ℂ n n sg μ q hq
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW n n) μ q
  by_cases hμ : μ = sg
  · subst hμ
    obtain ⟨c, hc⟩ := bs_hwspace μ hsg _ hmem hw'
    rw [hc, H.smulr, h0, mul_zero]
  · exact H.hw_weight hsg μ hμ _ hmem hw'
end Formalism.BranchingDeterminantCap.BsForm
