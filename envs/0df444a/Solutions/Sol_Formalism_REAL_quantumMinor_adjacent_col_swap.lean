-- Prove2me | solution 1 for Formalism.REAL.quantumMinor_adjacent_col_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:10.116481+00:00
-- url     : https://prove2.me/submissions/67695ad2-4d8e-4199-b2b3-7115db6832c5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_sum_term
import Theorems.Thm_Formalism_REAL_quantumMinorTerm_adjacent_swap
import Theorems.Thm_Formalism_REAL_eq_zero_of_add_self_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = - qminor E a b u := by
  have hsgn : Equiv.Perm.sign (Equiv.swap i.castSucc i.succ) = -1 :=
    Equiv.Perm.sign_swap (ne_of_lt Fin.castSucc_lt_succ)
  have reindex : ∀ bb : Fin (m + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
        exchangeTwo_self_eq_one E a bb u (σ * Equiv.swap i.castSucc i.succ) = - qminor E a bb u := by
    intro bb
    rw [quantumMinor_eq_sum_term, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i.castSucc i.succ)) _ _ (fun σ => ?_)
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, hsgn, Units.val_neg, Int.cast_neg, mul_neg,
      mul_one, neg_mul, neg_neg]
  have hsum : ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
        + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
        - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ)) = 0 := by
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [quantumMinorTerm_adjacent_swap E hE a b i u σ, mul_zero]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [reindex, reindex, ← quantumMinor_eq_sum_term, ← quantumMinor_eq_sum_term] at hsum
  have hX : qminor E a b u + qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = 0 := by
    apply eq_zero_of_add_self_eq_zero
    convert hsum using 1
    abel
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hX
end Formalism.REAL
