-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.capDet_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:30.754741+00:00
-- url     : https://prove2.me/submissions/8e826504-ccc0-432e-a3ee-c78858f28a21

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_tri
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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (v : M) (μ : Fin n → ℤ)
    (hr : ∀ l j, l < j → E l j v = 0) (hw : ∀ s, E s s v = ((μ s : ℤ) : R) • v) :
    capDet E u v = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - μ j) : ℤ) : R) • v := by
  have hα : ∀ α : Equiv.Perm (Fin n),
      ((∀ k, α k = k) → bmM E u α id v = (∏ k : Fin n, ((u + ((k : ℕ) : ℤ) - μ k : ℤ) : R)) • v) ∧
      ((¬ ∀ k, α k = k) → bmM E u α id v = 0) := by
    intro α
    unfold bmM
    refine bmA_tri v _ _ (fun k => α k = k) ?_ ?_
    · intro k hk
      simp only [bmF, id_eq, hk, if_true, LinearMap.sub_apply, hw]
      rw [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul R, ← sub_smul]
      push_cast
      rfl
    · intro k hk hj
      have hlt : α k < k := by
        rcases lt_trichotomy (α k) k with h | h | h
        · exact h
        · exact absurd h hk
        · exact absurd (α.injective (hj _ h)) hk
      simp only [bmF, id_eq, hk, if_false, LinearMap.sub_apply, hr _ _ hlt, LinearMap.zero_apply, sub_zero]
  unfold capDet bmPi
  rw [LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [LinearMap.smul_apply, (hα 1).1 (fun k => rfl)]
    simp
  · intro α _ hne
    have : ¬ ∀ k, α k = k := fun h => hne (Equiv.ext h)
    rw [LinearMap.smul_apply, (hα α).2 this, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.BranchingDeterminantCap
