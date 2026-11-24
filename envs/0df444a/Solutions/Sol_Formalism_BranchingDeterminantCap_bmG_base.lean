-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:41.813406+00:00
-- url     : https://prove2.me/submissions/cd874024-1873-4b10-8391-8a0ead683817

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_one
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_pow
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor1
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_cast
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_of_succ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_minor_empty
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (lam : Fin n → ℕ) (h : ∀ i : Fin n, nuNext lam i = 0) :
    ∃ G, bmLift R n lam lam 1 G := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, bmG_cast (bmLift_one R 0) (Subsingleton.elim _ _) (Subsingleton.elim _ _) rfl rfl⟩
  · have hs : 0 + 1 ≤ n := hn
    have h1 := bmLift_pow (bmLift_minor1 R n (Fin.elim0 : Fin 0 → Fin n) hs) (lam ⟨0, hn⟩)
    have hz : ∀ t : Fin n, t.val ≠ 0 → lam t = 0 := by
      intro t ht
      have hlt : t.val - 1 < n := by have := t.isLt; omega
      rw [← bmG_nuNext_of_succ lam ⟨t.val - 1, hlt⟩ t (by simp; omega)]
      exact h _
    refine ⟨_, bmG_cast h1 ?_ ?_ ?_ rfl⟩
    · funext t
      simp only [Pi.smul_apply, initW, smul_eq_mul]
      by_cases ht : t.val = 0
      · have : t = ⟨0, hn⟩ := Fin.ext ht
        rw [this]; simp
      · rw [if_neg (by omega), hz t ht, mul_zero]
    · funext t
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases ht : t.val = 0
      · have : t = ⟨0, hn⟩ := Fin.ext ht
        rw [this]; simp
      · rw [if_neg (fun hh => ht (by rw [hh])), hz t ht, mul_zero]
    · rw [bmG_minor_empty, one_pow]
end Formalism.BranchingDeterminantCap
