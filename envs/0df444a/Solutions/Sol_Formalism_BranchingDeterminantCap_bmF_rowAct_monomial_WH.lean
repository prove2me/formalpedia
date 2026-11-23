-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_monomial_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:17.949944+00:00
-- url     : https://prove2.me/submissions/662b8a3e-e537-4898-92f8-a8020cd2ecf6

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_isWeightedHomogeneous_smul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_aeval_monomial_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_var_WH

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
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (m : Fin (n + 1) × Fin n →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w (rowAct R (extM R g) (monomial m c : BP R n)) (Finsupp.weight w m) := by
  have hm : (monomial m c : BP R n) = c • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul]
  exact isWeightedHomogeneous_smul (bm_aeval_monomial_WH w _ (fun v => bmF_rowAct_var_WH R w hw g v) m) c
end Formalism.BranchingDeterminantCap
