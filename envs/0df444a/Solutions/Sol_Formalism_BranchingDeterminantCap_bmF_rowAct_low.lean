-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:14.530645+00:00
-- url     : https://prove2.me/submissions/f9f224f9-5890-42b1-8727-e4d642257a61

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zW_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_monomial_WH

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
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (D : ℤ) (L : BP R n)
    (hL : IsLow D L) : IsLow D (rowAct R (extM R g) L) := by
  classical
  intro m' hm'
  rw [L.as_sum, map_sum] at hm'
  obtain ⟨d, hd, hmd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')
  have hW := bmF_rowAct_monomial_WH R (zW n)
    (fun a b s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) g d (coeff d L)
  rw [hW (mem_support_iff.mp hmd)]
  exact hL d hd
end Formalism.BranchingDeterminantCap
