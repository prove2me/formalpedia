-- Prove2me | solution 1 for CircStability.Main.f_split
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:24:35.849987+00:00
-- url     : https://prove2.me/submissions/1ee8f2ac-de9e-4757-b4a4-02280be2ffa1

import Mathlib
import Definitions.Def_CircStability_Main_Setting
open Finset SimpleGraph

namespace Aux_CircStability_f_split
open CircStability.Main

theorem card_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    #G.edgeFinset ≤ edgesOffCycle G S + edgesOnCycle G S := by
  unfold edgesOffCycle edgesOnCycle
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro e he
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases h : ∃ v ∈ e, v ∉ S
  · refine Or.inl ⟨?_, h⟩
    convert he
  · push_neg at h
    refine Or.inr ⟨?_, h⟩
    convert he

theorem part1 (n c : ℕ) (hcn : c ≤ n) :
    fNum n (c / 2 - 1) c = (c / 2 - 1) * (n - c) + hNum (c + 1) (c / 2 - 1) := by
  unfold fNum hNum
  have e1 : c - (c / 2 - 1) + 1 = c + 1 - (c / 2 - 1) := by omega
  rw [e1]
  have e2 : (c / 2 - 1) * (n - c + (c / 2 - 1) - 1) =
      (c / 2 - 1) * (n - c) + (c / 2 - 1) * (c / 2 - 1 - 1) := by
    rcases Nat.eq_zero_or_pos (c / 2 - 1) with h0 | hpos
    · rw [h0]; simp
    · rw [← mul_add]; congr 1; omega
  rw [e2]
  ring

end Aux_CircStability_f_split

open CircStability.Main in
theorem solution (n c : ℕ) (hcn : c ≤ n) :
    fNum n (c / 2 - 1) c = (c / 2 - 1) * (n - c) + hNum (c + 1) (c / 2 - 1) ∧
      ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], ∀ S : Finset (Fin n),
        fNum n (c / 2 - 1) c < #G.edgeFinset →
          (c / 2 - 1) * (n - c) < edgesOffCycle G S ∨ hNum (c + 1) (c / 2 - 1) < edgesOnCycle G S := by
  have p1 := Aux_CircStability_f_split.part1 n c hcn
  refine ⟨p1, ?_⟩
  intro G _ S h
  have hle := Aux_CircStability_f_split.card_le G S
  rw [p1] at h
  generalize (c / 2 - 1) * (n - c) = A at *
  generalize hNum (c + 1) (c / 2 - 1) = B at *
  generalize edgesOffCycle G S = X at *
  generalize edgesOnCycle G S = Y at *
  generalize #G.edgeFinset = Z at *
  omega
