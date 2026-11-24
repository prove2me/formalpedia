-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.branch_scale_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:19.792272+00:00
-- url     : https://prove2.me/submissions/4998878f-8f6f-4c18-9201-f0c3d2fcdfed

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_left
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_right
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_zScale_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_coeff_rowAct_diag
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
theorem _root_.solution : BranchScale := by
  intro n k d t F hF
  have h1 : rowAct ℂ (zScale n t) F = ((t : ℂ) ^ d) • F := by
    ext m
    rw [zScale, ldrow_coeff_rowAct_diag, bs_zScale_prod, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ F.support
    · rw [hF m hm, mul_comm]
    · rw [notMem_support_iff.mp hm]; simp
  refine ⟨h1, ?_⟩
  rw [h1, bs_fock_smul_left, bs_fock_smul_right]
  have : star ((t : ℂ) ^ d) = (t : ℂ) ^ d := by simp
  rw [this, two_mul, pow_add]; ring
end Formalism.BranchingDeterminantCap
