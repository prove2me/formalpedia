-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_diag_tall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:56.438645+00:00
-- url     : https://prove2.me/submissions/ff37874b-9bc1-45b4-914d-c78bcb39f3cd

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (ν : Fin n → ℕ) (s : Fin n) (hs : r ≤ s.val) (hνs : 0 < ν s)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) :
    eval D g = 0 := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_eq_zero
  intro m hm
  have hw : Finsupp.weight (colW r n) m = ν := hg (mem_support_iff.mp hm)
  have hcol : ∑ a : Fin r, m (a, s) ≠ 0 := by
    rw [← lhwline_weight_col, hw]
    exact Nat.pos_iff_ne_zero.mp hνs
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcol
  have hDa : D (a, s) = 0 := hD a s (by have := a.isLt; omega)
  rw [Finset.prod_eq_zero (Finset.mem_univ (a, s)) (by rw [hDa, zero_pow ha]), mul_zero]
end Formalism.GradedWeylDivisibility
