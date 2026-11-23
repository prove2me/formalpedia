-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_zScale_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:05.395463+00:00
-- url     : https://prove2.me/submissions/85df674e-5f6e-41c9-9dcd-db569939f639

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_rowAct_diag_eq
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
theorem _root_.solution (n : ℕ) (lam : Fin n → ℕ) (t : ℝ) :
    rowAct ℂ (zScale n t) (hw ℂ (Nat.le_succ n) lam) = hw ℂ (Nat.le_succ n) lam := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow]
  congr 1
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  have hne : Fin.castLE (by omega : s.val + 1 ≤ n + 1) p ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have h1 := p.isLt
    have h2 := s.isLt
    omega
  simp [zScale, ldrow_rowAct_diag_eq, hne]
end Formalism.BranchingDeterminantCap
