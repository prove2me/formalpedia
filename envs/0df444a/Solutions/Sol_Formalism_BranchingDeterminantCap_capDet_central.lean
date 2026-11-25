-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.capDet_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:02.032729+00:00
-- url     : https://prove2.me/submissions/b561de8c-5789-4725-b65d-ea4c2e13d5cc

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_comm_prod
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_sub
import Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_bmA_prod_update_zero__a3a3001d3055
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_Pi_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_row_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_comm_entry
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
    (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (k l : Fin n) : Commute (E k l) (capDet E u) := by

  have hM : ∀ α : Equiv.Perm (Fin n), E k l * bmM E u α id - bmM E u α id * E k l =
      bmM E u (Function.update id l k ∘ α) id - bmM E u α (Function.update id k l) := by
    intro α
    unfold bmM
    rw [bmA_comm_prod]
    simp only [bmA_comm_entry E u hE, bmA_prod_update_sub, Finset.sum_sub_distrib, id_eq]
    congr 1
    · rw [Finset.sum_eq_single (α.symm l)]
      · rw [if_pos (by simp)]
        congr 2
        funext q
        by_cases hq : q = α.symm l
        · subst hq; simp
        · rw [Function.update_of_ne hq]
          have : α q ≠ l := fun h => hq (by rw [← h]; simp)
          simp [Function.update_of_ne this]
      · intro q _ hq
        have : l ≠ α q := fun h => hq (by rw [h]; simp)
        rw [if_neg this, bmA_prod_update_zero']
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
        congr 2
        funext q
        by_cases hq : q = k
        · subst hq; simp
        · rw [Function.update_of_ne hq, Function.update_of_ne hq]; rfl
      · intro q _ hq
        rw [if_neg (Ne.symm hq), bmA_prod_update_zero']
      · intro h; exact absurd (Finset.mem_univ _) h
  have hsum : E k l * capDet E u - capDet E u * E k l =
      (∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (Function.update id l k ∘ α) id) -
        bmPi E u (Function.update id k l) := by
    unfold capDet bmPi
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hM, smul_sub]
  have hzero : E k l * capDet E u - capDet E u * E k l = 0 := by
    rw [hsum]
    by_cases hkl : k = l
    · subst hkl
      have hid : Function.update (id : Fin n → Fin n) k k = id := Function.update_eq_self k id
      rw [hid]
      unfold bmPi
      simp only [Function.id_comp, sub_self]
    · rw [bmA_row_zero E u h2 (Function.update id l k) id k l hkl (by simp [Function.update_of_ne hkl]),
        bmA_Pi_zero E u hE h2 (Function.update id k l) k l hkl (by simp [Function.update_of_ne (Ne.symm hkl)]),
        sub_zero]
  exact sub_eq_zero.1 hzero
end Formalism.BranchingDeterminantCap
