-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_arith_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:06.267696+00:00
-- url     : https://prove2.me/submissions/83d9436f-fe2b-4117-bd1b-1f0c73828857

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (l d m e : ℕ) (hl : l.Prime) (hm : ¬ l ∣ m)
    (h : ∀ i ≤ d, d.choose i ∣ m * l ^ e) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l d ≤ e := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  refine Finset.sup_le (fun i hi => ?_)
  have hi' : i ≤ d := by rw [Finset.mem_range] at hi; omega
  have hc0 : d.choose i ≠ 0 := (Nat.choose_pos hi').ne'
  have hne : m * l ^ e ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hl.ne_zero)
  have h1 := Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hc0 hne).mpr (h i hi')) l
  have h2 : (m * l ^ e).factorization l = e := by
    rw [Nat.factorization_mul hm0 (pow_ne_zero _ hl.ne_zero)]
    simp [Nat.factorization_eq_zero_of_not_dvd hm, hl.factorization_self]
  rw [h2] at h1
  exact h1
end Formalism.CohomologicalDescent.LA
