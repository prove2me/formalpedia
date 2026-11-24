-- Prove2me | solution 1 for Formalism.REAL.casKHW_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:07.192334+00:00
-- url     : https://prove2.me/submissions/2431b1c6-da32-46a6-a5be-f30fc4ba1be2

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
import Theorems.Thm_Formalism_REAL_casKHW_two_rhoC

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b, casKHW_coef ε μ a b = nsq (μ + rhoC ε) - nsq (rhoC ε) := by
  have hpt : ∀ a b, casKHW_coef ε μ a b =
      (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0) -
        (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    unfold casKHW_coef
    by_cases h : ε a = ε b
    · rcases lt_trichotomy a b with hab | rfl | hab
      · simp [h, hab, ne_of_lt hab]
      · simp
      · simp [h, ne_of_gt hab, not_lt_of_gt hab]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      by_cases hab : a = b
      · exact absurd (congrArg ε hab) h
      · simp [h, h', hab]
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ a : Fin n, ∑ b : Fin n, (if a = b then μ a ^ 2 else 0) = ∑ a, μ a ^ 2 := by
    simp
  have e2 : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε a = ε b then μ b else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) := by
    rw [Finset.sum_comm]
  have e3 : ∀ a, ∑ b : Fin n, (if a < b ∧ ε b = ε a then μ a else 0) -
      ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) = μ a * (2 * rhoC ε a) := by
    intro a
    rw [casKHW_two_rhoC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [e1, e2, add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e3]
  unfold nsq dot
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring
end Formalism.REAL
