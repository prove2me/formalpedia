-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_rowGen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:24.166959+00:00
-- url     : https://prove2.me/submissions/6dff45ac-bb87-40cd-96b6-3efe9fc822d1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_rowDiv_zero
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
variable {K : Type*} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) K)
    (h : ∀ k : ℕ, 1 ≤ k → rowDiv K a b k g = 0) : rowGen K a b g = Polynomial.C g := by
  ext1 k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 := lhwline_rowDiv_zero a b g
    simp only [rowDiv] at h0
    rw [h0, Polynomial.coeff_C_zero]
  · have h1 := h k hk
    simp only [rowDiv] at h1
    rw [h1, Polynomial.coeff_C, if_neg (by omega)]
end Formalism.GradedWeylDivisibility
