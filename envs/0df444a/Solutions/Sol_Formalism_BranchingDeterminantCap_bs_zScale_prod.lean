-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_zScale_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:05.627431+00:00
-- url     : https://prove2.me/submissions/fb9498ed-e39e-4b9d-998b-ed5363e72b78

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
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
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (n : ℕ) (t : ℝ) (e : Fin (n + 1) → ℕ) :
    ∏ a, (if a = Fin.last n then (t : ℂ) else 1) ^ e a = (t : ℂ) ^ e (Fin.last n) := by
  rw [Finset.prod_eq_single (Fin.last n)]
  · simp
  · intro b _ hb; simp [hb]
  · simp
end Formalism.BranchingDeterminantCap
