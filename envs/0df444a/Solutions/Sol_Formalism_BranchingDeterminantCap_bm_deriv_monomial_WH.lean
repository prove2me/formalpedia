-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_deriv_monomial_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:03.828845+00:00
-- url     : https://prove2.me/submissions/34e0c0be-54fe-4fa0-bc63-365790e0146f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (δ : B)
    (f : σ → MvPolynomial σ R) (hf : ∀ v, IsWeightedHomogeneous w (f v) (w v + δ)) (m : σ →₀ ℕ) :
    IsWeightedHomogeneous w (mkDerivation R f (monomial m 1)) (Finsupp.weight w m + δ) := by
  rw [mkDerivation_monomial, one_smul, Finsupp.sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
  have hm : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsplit : m = (m - Finsupp.single i 1) + Finsupp.single i 1 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hm)).symm
  have hw1 : Finsupp.weight w (Finsupp.single i 1) = w i := by
    simp [Finsupp.weight_apply]
  have e : Finsupp.weight w m + δ = Finsupp.weight w (m - Finsupp.single i 1) + (w i + δ) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hw1, add_assoc]
  rw [e, smul_eq_mul]
  exact (isWeightedHomogeneous_monomial _ _ _ rfl).mul (hf i)
end Formalism.BranchingDeterminantCap
