-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:44.016796+00:00
-- url     : https://prove2.me/submissions/4bf3ccd3-cb2f-4688-a95b-285d13fbceb8

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mono_zero
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
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (hn : n ≤ r) (ν : Fin n → ℕ)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) :
    eval D g = coeff (lhwline_mnu hn ν) g * ∏ v, D v ^ (lhwline_mnu hn ν) v := by
  rw [MvPolynomial.eval_eq', Finset.sum_eq_single (lhwline_mnu hn ν)]
  · intro m hm hne
    rw [lhwline_mono_zero hn ν g hg D hD m hm hne, mul_zero]
  · intro h
    simp only [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul]
end Formalism.GradedWeylDivisibility
