-- Prove2me | solution 1 for EngageInfo.eq_6_vstar
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:31:44.14068+00:00
-- url     : https://prove2.me/submissions/36037b43-9566-49db-b94e-5fbe89d0e1b1

import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Theorems.Thm_EngageInfo_eq_5_price_response
import Theorems.Thm_EngageInfo_lemma_1

namespace Aux_EngageInfo_eq_6
open EngageInfo CollabProject.TimeDep

lemma effort_false (M : Params) : effort M false = 0 := rfl
lemma effort_true (M : Params) : effort M true = M.ebar := rfl

lemma br_profit_eq (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) {p : ℝ}
    (hbr : SequentialGame.IsBR0 (subgame M α).payoff0 b p) :
    sellerProfit M α (effort M b) p =
      max (M.θL + effort M b - M.c) (α * (M.θH + effort M b - M.c)) := by
  have hgreat := (eq_5_price_response M α hα b).2
  rcases hgreat.1 with ⟨pStar, hpStar⟩
  refine le_antisymm (hgreat.2 ⟨p, rfl⟩) ?_
  rw [← hpStar]
  exact hbr pStar

end Aux_EngageInfo_eq_6

open EngageInfo CollabProject.TimeDep Aux_EngageInfo_eq_6

theorem solution (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest (spePayoffs M α)
        (if M.m ≤ α ∧ α ≤ M.αbar then M.θL + M.ebar - M.c else max (M.θL - M.c) (α * (M.θH - M.c))) ∧
    vstar M α =
        (if M.m ≤ α ∧ α ≤ M.αbar then M.θL + M.ebar - M.c else max (M.θL - M.c) (α * (M.θH - M.c))) := by
  have hl1 := lemma_1 M α hα
  have hgreat : IsGreatest (spePayoffs M α)
      (if M.m ≤ α ∧ α ≤ M.αbar then M.θL + M.ebar - M.c else max (M.θL - M.c) (α * (M.θH - M.c))) := by
    split_ifs with hm
    · rcases (hl1.2.1 hm).1 with ⟨P, hP⟩
      have hα0 : M.α₀ ≤ α := le_trans (le_max_left _ _) hm.1
      have hebar_pos : 0 < M.ebar := by linarith [M.k_pos, M.k_lt_ebar]
      have hHbar_pos : 0 < M.θH + M.ebar - M.c := by linarith [M.c_lt_θL, M.θL_lt_θH, hebar_pos]
      have hbar_le : α * (M.θH + M.ebar - M.c) ≤ M.θL + M.ebar - M.c := by
        have h := hm.2
        unfold Params.αbar Params.alpha at h
        exact (le_div_iff₀ hHbar_pos).mp h
      have h0_ge : M.θL - M.c ≤ α * (M.θH - M.c) := by
        have h := hα0
        unfold Params.α₀ Params.alpha at h
        simp only [add_zero] at h
        exact (div_le_iff₀ (by linarith [M.c_lt_θL, M.θL_lt_θH])).mp h
      refine ⟨⟨true, P, hP, ?_⟩, ?_⟩
      · have hprof := br_profit_eq M α hα true (hP.1 true)
        rw [effort_true, max_eq_left hbar_le] at hprof
        rw [effort_true]
        exact hprof.symm
      · rintro x ⟨b', P', hP', rfl⟩
        have hprof := br_profit_eq M α hα b' (hP'.1 b')
        cases b'
        · rw [effort_false, add_zero, add_zero, max_eq_right h0_ge] at hprof
          rw [effort_false, hprof]
          have hmul : α * (M.θH - M.c) ≤ α * (M.θH + M.ebar - M.c) :=
            mul_le_mul_of_nonneg_left (by linarith) hα.1
          linarith
        · rw [effort_true, max_eq_left hbar_le] at hprof
          rw [effort_true, hprof]
    · rcases hl1.1 with ⟨b, P, hP⟩
      have hb : b = false := hl1.2.2 hm b P hP
      subst hb
      refine ⟨⟨false, P, hP, ?_⟩, ?_⟩
      · have hprof := br_profit_eq M α hα false (hP.1 false)
        rw [effort_false, add_zero, add_zero] at hprof
        rw [effort_false]
        exact hprof.symm
      · rintro x ⟨b', P', hP', rfl⟩
        have hb' : b' = false := hl1.2.2 hm b' P' hP'
        subst hb'
        have hprof := br_profit_eq M α hα false (hP'.1 false)
        rw [effort_false, add_zero, add_zero] at hprof
        rw [effort_false, hprof]
  exact ⟨hgreat, hgreat.csSup_eq⟩
