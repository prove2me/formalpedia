-- Prove2me | solution 1 for Freiman.middleRepair_frame_prefix_completion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:22.162711+00:00
-- url     : https://prove2.me/submissions/ae0f5e2a-aa3c-4c79-939f-31041570796e

import Theorems.Thm_Freiman_middleRepair_frame_compatible_nonempty
import Theorems.Thm_Freiman_middleRepair_frame_alphabet_bound
import Theorems.Thm_Freiman_middleRepair_frame_prefix_compatible
import Theorems.Thm_Freiman_middleRepair_frame_completion_closed
import Theorems.Thm_Freiman_middle_compatible_monotone
import Theorems.Thm_Freiman_bounded_words_subsequence
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ p : ℕ → MiddleCore, (∀ n : ℕ, middleProper (p n) (p (n+1))) →
  ∃ a : ℤ → ℕ+, ∀ n : ℕ, middleCompatible (p n) a := by
  intro p hp
  choose A hA using fun n => middleRepair_frame_compatible_nonempty (p n)
  obtain ⟨M,hM⟩ := middleRepair_frame_alphabet_bound (p 0)
  have hb : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, (A n i : ℕ)≤M := by
    intro i
    exact Filter.Eventually.of_forall fun n => hM (A n)
      (middleRepair_frame_prefix_compatible middle_compatible_monotone p hp 0 n (Nat.zero_le n) (A n) (hA n)) i
  obtain ⟨v,hv,a,_,ha⟩ := bounded_words_subsequence A M hb
  refine ⟨a,?_⟩
  intro k
  apply middleRepair_frame_completion_closed (p k) (fun n => A (v n)) a ha
  apply Filter.eventually_atTop.2
  refine ⟨k,?_⟩
  intro n hn
  exact middleRepair_frame_prefix_compatible middle_compatible_monotone p hp k (v n)
    (le_trans hn (hv.id_le n)) (A (v n)) (hA (v n))
