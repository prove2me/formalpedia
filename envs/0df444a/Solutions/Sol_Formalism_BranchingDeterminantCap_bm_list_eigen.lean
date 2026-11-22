-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_list_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:18.12653+00:00
-- url     : https://prove2.me/submissions/fbc37d8c-24a3-4226-ad1e-187b66d5ad35

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (C : ℤ → Module.End R M)
    (χ : ℤ → ℤ) (v : M) (h : ∀ u, C u v = ((χ u : ℤ) : R) • v) (ℓ : List ℤ) :
    (ℓ.map C).prod v = (((ℓ.map χ).prod : ℤ) : R) • v := by
  induction ℓ with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    show C a ((List.map C t).prod v) = _
    rw [ih, map_smul, h, smul_smul]
    congr 1
    push_cast
    ring
end Formalism.BranchingDeterminantCap
