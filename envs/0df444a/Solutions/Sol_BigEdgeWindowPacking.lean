-- Prove2me | solution 1 for BigEdgeWindowPacking
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:30.333858+00:00
-- url     : https://prove2.me/submissions/fc7fe33f-977b-45c2-b225-cb4e700c2a6d

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_BigEdgeWindowPacking

set_option autoImplicit false
open Set
theorem _root_.solution (k : ℕ) (s : ℕ → ℝ) (δ a b : ℝ) (hδ : 0 < δ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) (hab : a ≤ b) :
    (((Finset.Icc 1 k).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ δ ≤ s j - s (j - 1))).card : ℝ) * δ ≤ b - a := by
-- BODY
  have key : ∀ K : ℕ, (∀ p q : ℕ, p ≤ q → q ≤ K → s p ≤ s q) → ∀ c : ℝ, a ≤ c →
      (((Finset.Icc 1 K).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ c ∧ δ ≤ s j - s (j - 1))).card : ℝ) * δ ≤ c - a := by
    intro K
    induction K with
    | zero =>
      intro _ c hac
      have hE : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
        apply Finset.Icc_eq_empty; omega
      rw [hE]
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
      linarith
    | succ m ih =>
      intro hm c hac
      have hmm : ∀ p q : ℕ, p ≤ q → q ≤ m → s p ≤ s q := fun p q hpq hq =>
        hm p q hpq (hq.trans (Nat.le_succ m))
      have hins : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnotmem : (m + 1) ∉ Finset.Icc 1 m := by
        simp only [Finset.mem_Icc]; omega
      rw [hins, Finset.filter_insert]
      by_cases hP : a ≤ s (m + 1 - 1) ∧ s (m + 1) ≤ c ∧ δ ≤ s (m + 1) - s (m + 1 - 1)
      · rw [if_pos hP]
        obtain ⟨hPa, hPc, hPd⟩ := hP
        simp only [Nat.add_sub_cancel] at hPa hPd
        rw [Finset.card_insert_of_notMem (fun hmem => hnotmem (Finset.mem_of_mem_filter _ hmem))]
        -- the retained indices `j ≤ m` all satisfy `s j ≤ s m`
        have hsub : (Finset.Icc 1 m).filter
            (fun j => a ≤ s (j - 1) ∧ s j ≤ c ∧ δ ≤ s j - s (j - 1)) ⊆
            (Finset.Icc 1 m).filter
              (fun j => a ≤ s (j - 1) ∧ s j ≤ s m ∧ δ ≤ s j - s (j - 1)) := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
          obtain ⟨⟨hj1, hjm⟩, hja, _, hjd⟩ := hj
          exact ⟨⟨hj1, hjm⟩, hja, hmm j m hjm le_rfl, hjd⟩
        have hcard := Finset.card_le_card hsub
        have hih := ih hmm (s m) hPa
        have hmono' : (((Finset.Icc 1 m).filter
            (fun j => a ≤ s (j - 1) ∧ s j ≤ c ∧ δ ≤ s j - s (j - 1))).card : ℝ) ≤
            (((Finset.Icc 1 m).filter
              (fun j => a ≤ s (j - 1) ∧ s j ≤ s m ∧ δ ≤ s j - s (j - 1))).card : ℝ) := by
          exact_mod_cast hcard
        have hstep : (((Finset.Icc 1 m).filter
            (fun j => a ≤ s (j - 1) ∧ s j ≤ c ∧ δ ≤ s j - s (j - 1))).card : ℝ) * δ ≤
            s m - a := le_trans (by nlinarith [hδ.le]) hih
        push_cast
        nlinarith
      · rw [if_neg hP]
        exact ih hmm c hac
  have hm : ∀ p q : ℕ, p ≤ q → q ≤ k → s p ≤ s q := by
    intro p q hpq hq
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hpq.trans hq⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq
  exact key k hm b hab
