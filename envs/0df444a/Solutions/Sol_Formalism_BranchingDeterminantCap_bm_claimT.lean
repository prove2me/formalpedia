-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_claimT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:32.071266+00:00
-- url     : https://prove2.me/submissions/83b8e955-8875-494d-8ac7-7a9be1be3d60

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_weight_zW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_tri
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ) (H : BP R n)
    (hH : H ∈ dualWeyl R (n + 1) n lam)
    (hrow : ∀ m ∈ H.support, ∀ a : Fin n, rowDeg m a.castSucc = sg a)
    (hlow : IsLow (omg fun s => (lam s : ℤ) - (sg s : ℤ)) H) : H = 0 := by
  by_contra hne
  set m := (colLex (n + 1) n).degree H with hmdef
  have hm : m ∈ H.support := MonomialOrder.degree_mem_support hne
  have hint : Interlaced m := leadInterlaced R (n + 1) n lam H hH hne
  have htri := bmC_tri m hint (Nat.le_succ n)
  have hcol := colSums R (n + 1) n lam H hH m hm
  have hr := hrow m hm
  have hl := hlow m hm
  unfold omg at hl
  simp only [bm_weight_zW] at hl

  have hcol' : ∀ s : Fin n, (lam s : ℤ) = (∑ a : Fin n, (m (a.castSucc, s) : ℤ)) + (m (Fin.last n, s) : ℤ) := by
    intro s
    rw [← hcol s, Fin.sum_univ_castSucc]
    push_cast
    rfl
  have hrow' : ∀ a : Fin n, (sg a : ℤ) = ∑ s : Fin n, (m (a.castSucc, s) : ℤ) := by
    intro a
    rw [← hr a]
    unfold rowDeg
    push_cast
    rfl
  have hkey : (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ∑ a : Fin n, (m (a.castSucc, s) : ℤ)) ≤
      ∑ a : Fin n, ((((a : ℕ) : ℤ)) + 1) * ∑ s : Fin n, (m (a.castSucc, s) : ℤ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro s _
    by_cases has : a.val < s.val
    · have : m (a.castSucc, s) = 0 := htri s.val s rfl a.castSucc (by simpa using has)
      rw [this]; simp
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (s : ℕ) ≤ (a : ℕ) := by omega
      have : ((s : ℕ) : ℤ) ≤ ((a : ℕ) : ℤ) := by exact_mod_cast this
      linarith
  have e1 : (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ((lam s : ℤ) - (sg s : ℤ))) =
      (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ∑ a : Fin n, (m (a.castSucc, s) : ℤ)) +
      (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * (m (Fin.last n, s) : ℤ)) -
      ∑ a : Fin n, ((((a : ℕ) : ℤ)) + 1) * ∑ s : Fin n, (m (a.castSucc, s) : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [hcol' s, hrow' s]
    ring
  rw [e1] at hl
  linarith
end Formalism.BranchingDeterminantCap
