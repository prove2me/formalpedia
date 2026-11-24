-- Prove2me | solution 1 for Formalism.CohomologicalDescent.we_msum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:56.026264+00:00
-- url     : https://prove2.me/submissions/6047d0a5-deca-4150-97ec-b381ec530869

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution (Y A Bm X : Multiset ℤ) (lo hi : ℤ) (hYA : Y ≤ A) (hA : A = Bm + X)
    (hc : Multiset.card Y = Multiset.card Bm) (hin : ∀ a ∈ A, lo ≤ a ∧ a ≤ hi) :
    |Bm.sum - Y.sum| ≤ (Multiset.card X : ℤ) * (hi - lo) := by
  subst hA
  have noMem : hi < lo → ∀ S : Multiset ℤ, (∀ a ∈ S, lo ≤ a ∧ a ≤ hi) → Multiset.card S = 0 := by
    intro hlt S hS
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne)
    have := hS a ha
    omega
  have hP : Y - Bm ≤ X := Multiset.sub_le_iff_le_add.2 (by rw [add_comm]; exact hYA)
  have hYs : Y.sum = (Y - Bm).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.sum_add]
  have hBs : Bm.sum = (Bm - Y).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.sum_add, Multiset.inter_comm]
  have hYc : Multiset.card Y = Multiset.card (Y - Bm) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.card_add]
  have hBc : Multiset.card Bm = Multiset.card (Bm - Y) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.card_add, Multiset.inter_comm]
  have hPQ : Multiset.card (Y - Bm) = Multiset.card (Bm - Y) := by omega
  have memP : ∀ a ∈ Y - Bm, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_of_le hYA (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha))
  have memQ : ∀ a ∈ Bm - Y, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_add.2 (Or.inl (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)))
  have memX : ∀ a ∈ X, lo ≤ a ∧ a ≤ hi := fun a ha => hin a (Multiset.mem_add.2 (Or.inr ha))
  have P1 := Multiset.sum_le_card_nsmul (Y - Bm) hi (fun a ha => (memP a ha).2)
  have P2 : Multiset.card (Y - Bm) • lo ≤ (Y - Bm).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memP a ha).1)
  have Q1 := Multiset.sum_le_card_nsmul (Bm - Y) hi (fun a ha => (memQ a ha).2)
  have Q2 : Multiset.card (Bm - Y) • lo ≤ (Bm - Y).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memQ a ha).1)
  rw [hPQ] at P1 P2
  simp only [nsmul_eq_mul] at P1 P2 Q1 Q2
  have hm : (Multiset.card (Bm - Y) : ℤ) * (hi - lo) ≤ (Multiset.card X : ℤ) * (hi - lo) := by
    by_cases h : lo ≤ hi
    · apply mul_le_mul_of_nonneg_right _ (by linarith)
      have := Multiset.card_le_card hP
      rw [hPQ] at this
      exact_mod_cast this
    · push_neg at h
      rw [noMem h _ memQ, noMem h X memX]
  rw [hYs, hBs, abs_le]
  constructor <;> linarith
end Formalism.CohomologicalDescent
