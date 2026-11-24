-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:05.004068+00:00
-- url     : https://prove2.me/submissions/4b27b680-c49a-4d1f-be3c-c8c7ca009b87

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (μ : Fin n → ℝ) :
    (∑ a, ∑ b, (if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0)
      else 0 : ℝ)) = ckv ε μ := by
  have hr : ∀ a, rhoC ε a = (∑ b, ((if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
      (if b < a ∧ ε b = ε a then (1 : ℝ) else 0))) / 2 := by
    intro a
    simp only [rhoC, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_sub_distrib]
  have hR : ckv ε μ = ∑ a, μ a ^ 2 + ∑ a, ∑ b, (if a < b ∧ ε b = ε a then μ a else 0)
      - ∑ a, ∑ b, (if b < a ∧ ε b = ε a then μ a else 0) := by
    unfold ckv nsq dot
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Pi.add_apply, hr a]
    have : (∑ b, (if a < b ∧ ε b = ε a then μ a else 0)) - ∑ b, (if b < a ∧ ε b = ε a then μ a else 0)
        = μ a * ∑ b, ((if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
          (if b < a ∧ ε b = ε a then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs <;> ring
    rw [add_sub_assoc, this]; ring
  rw [hR, Finset.sum_comm (f := fun a b => if b < a ∧ ε b = ε a then μ a else 0)]
  have hL : ∀ a b, (if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0)
      else 0 : ℝ) = (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0)
        - (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h2 | rfl | h2
    · by_cases h1 : ε a = ε b
      · simp [h1, h2, h2.ne]
      · have h1' : ¬ ε b = ε a := fun h => h1 h.symm
        simp [h1, h1', h2.ne]
    · simp
    · simp [h2.ne', not_lt.mpr h2.le]
  simp only [hL, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
end Formalism.REAL
