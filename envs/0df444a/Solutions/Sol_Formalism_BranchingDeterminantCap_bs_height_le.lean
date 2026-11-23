-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_height_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:40.157043+00:00
-- url     : https://prove2.me/submissions/7e99a305-b05f-41e0-aeeb-1bf4f67d624a

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_abel

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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (n : ℕ) (x y : Fin n → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin n with a.val < k, x a) ≤ ∑ a : Fin n with a.val < k, y a)
    (h2 : ∑ a, x a = ∑ a, y a) :
    ∑ a : Fin n, (a.val : ℤ) * (y a : ℤ) ≤ ∑ a : Fin n, (a.val : ℤ) * (x a : ℤ) := by
  rw [bs_abel, bs_abel]
  refine Finset.sum_le_sum fun k _ => ?_
  have e1 := h1 (k + 1)
  have e1' : (∑ a : Fin n with a.val < k + 1, (x a : ℤ)) ≤ ∑ a : Fin n with a.val < k + 1, (y a : ℤ) := by
    exact_mod_cast e1
  have e2' : (∑ a, (x a : ℤ)) = ∑ a, (y a : ℤ) := by exact_mod_cast h2
  linarith
end Formalism.BranchingDeterminantCap
