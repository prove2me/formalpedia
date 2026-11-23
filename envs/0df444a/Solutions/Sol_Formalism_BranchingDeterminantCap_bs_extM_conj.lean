-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_extM_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:05.260805+00:00
-- url     : https://prove2.me/submissions/8c3307d0-4145-4d8d-89fb-d3e1cde1087a

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
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (extM ℂ g).conjTranspose = extM ℂ g.conjTranspose := by
  ext a b
  simp only [Matrix.conjTranspose_apply, extM, Matrix.of_apply]
  by_cases h : a.val < n ∧ b.val < n
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]
    by_cases e : a = b
    · subst e; simp
    · rw [if_neg e, if_neg (Ne.symm e)]; simp
end Formalism.BranchingDeterminantCap
