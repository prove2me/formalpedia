-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_IL_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:51.551891+00:00
-- url     : https://prove2.me/submissions/44fbb902-6d74-4db6-809f-b761fed1b426

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_lamZ_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_lamZ_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) : bmIL lam sg := by
  intro i
  have h1 : (sg i : ℤ) ≤ lam i := by
    have := (hI i).1
    rwa [bmH_lamZ_castSucc] at this
  have h2 : (nuNext lam i : ℤ) ≤ sg i := by
    have := (hI i).2
    rwa [bmH_lamZ_succ] at this
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
end Formalism.BranchingDeterminantCap
