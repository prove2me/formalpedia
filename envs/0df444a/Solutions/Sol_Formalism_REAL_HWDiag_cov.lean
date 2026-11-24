-- Prove2me | solution 1 for Formalism.REAL.HWDiag_cov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:48.593586+00:00
-- url     : https://prove2.me/submissions/07e8ddd6-6eb1-4da0-8bca-94a993da8d06

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag

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
theorem _root_.solution {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) :
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0) := by
  intro k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow]
    have lhs : E c d * (if a = b then (1:A) else 0) - (if a = b then (1:A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [lhs]
    by_cases h : d = a ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have h1 : (if d = a then (if c = b then (1:A) else 0) else 0) = 0 := by
        split_ifs with h2 h3 <;> simp_all
      have h2 : (if b = c then (if a = d then (1:A) else 0) else 0) = 0 := by
        split_ifs with h2 h3 <;> simp_all
      rw [h1, h2, sub_zero]
  | succ k ih =>
    intro a b c d
    have key : ∀ e, E c d * (epow E k a e * E e b) - (epow E k a e * E e b) * E c d
        = (E c d * epow E k a e - epow E k a e * E c d) * E e b
          + epow E k a e * (E c d * E e b - E e b * E c d) := by
      intro e; noncomm_ring
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun e _ => key e)]
    simp only [ih, hE c d]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
        mul_ite] <;> abel
end Formalism.REAL
