-- Prove2me | solution 1 for EngageInfo.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:25:56.916918+00:00
-- url     : https://prove2.me/submissions/a41ab003-46ef-47d4-b208-158272fc4b85

import Definitions.Def_CollabProject_TimeDep_Game
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_subgame
import Definitions.Def_EngageInfo_vstar
import Theorems.Thm_EngageInfo_eq_5_price_response

namespace Aux_EngageInfo_lemma_1
open EngageInfo CollabProject.TimeDep

lemma effort_false (M : Params) : effort M false = 0 := rfl
lemma effort_true (M : Params) : effort M true = M.ebar := rfl
lemma alpha_effort_false (M : Params) : M.alpha (effort M false) = M.α₀ := rfl
lemma alpha_effort_true (M : Params) : M.alpha (effort M true) = M.αbar := rfl

lemma Θ_pos (M : Params) : 0 < M.Θ := by
  unfold Params.Θ; linarith [M.θL_lt_θH]

lemma ebar_pos (M : Params) : 0 < M.ebar := by
  linarith [M.k_pos, M.k_lt_ebar]

lemma α₀_pos (M : Params) : 0 < M.α₀ := by
  unfold Params.α₀ Params.alpha
  exact div_pos (by linarith [M.c_lt_θL]) (by linarith [M.c_lt_θL, M.θL_lt_θH])

lemma br_iff (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) (p : ℝ) :
    SequentialGame.IsBR0 (subgame M α).payoff0 b p ↔
      ((α < M.alpha (effort M b) ∧ p = M.θL + effort M b) ∨
        (M.alpha (effort M b) < α ∧ p = M.θH + effort M b) ∨
        (α = M.alpha (effort M b) ∧ (p = M.θL + effort M b ∨ p = M.θH + effort M b))) :=
  (eq_5_price_response M α hα b).1 p

lemma br_low_of_le (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool)
    (hle : α ≤ M.alpha (effort M b)) :
    SequentialGame.IsBR0 (subgame M α).payoff0 b (M.θL + effort M b) := by
  rw [br_iff M α hα b]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl ⟨hlt, rfl⟩
  · exact Or.inr (Or.inr ⟨heq, Or.inl rfl⟩)

lemma br_high_of_ge (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool)
    (hge : M.alpha (effort M b) ≤ α) :
    SequentialGame.IsBR0 (subgame M α).payoff0 b (M.θH + effort M b) := by
  rw [br_iff M α hα b]
  rcases lt_or_eq_of_le hge with hgt | heq
  · exact Or.inr (Or.inl ⟨hgt, rfl⟩)
  · exact Or.inr (Or.inr ⟨heq.symm, Or.inr rfl⟩)

lemma br_profit_eq (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) {p : ℝ}
    (hbr : SequentialGame.IsBR0 (subgame M α).payoff0 b p) :
    sellerProfit M α (effort M b) p =
      max (M.θL + effort M b - M.c) (α * (M.θH + effort M b - M.c)) := by
  have hgreat := (eq_5_price_response M α hα b).2
  rcases hgreat.1 with ⟨pStar, hpStar⟩
  refine le_antisymm (hgreat.2 ⟨p, rfl⟩) ?_
  rw [← hpStar]
  exact hbr pStar

lemma cust_false_L (M : Params) (α : ℝ) :
    customerPayoff M α false M.θL = α * M.Θ := by
  unfold customerPayoff engageCost Params.Θ
  rw [effort_false]
  have h1 : 0 ≤ M.θH + 0 - M.θL := by linarith [M.θL_lt_θH]
  have h2 : M.θL + 0 - M.θL = 0 := by ring
  have h3 : (if false = true then M.k else 0) = 0 := rfl
  rw [max_eq_left h1, h2, max_self, h3]
  ring

lemma cust_false_H (M : Params) (α : ℝ) :
    customerPayoff M α false M.θH = 0 := by
  unfold customerPayoff engageCost
  rw [effort_false]
  have h1 : M.θH + 0 - M.θH = 0 := by ring
  have h2 : M.θL + 0 - M.θH ≤ 0 := by linarith [M.θL_lt_θH]
  have h3 : (if false = true then M.k else 0) = 0 := rfl
  rw [h1, max_self, max_eq_right h2, h3]
  ring

lemma cust_true_L (M : Params) (α : ℝ) :
    customerPayoff M α true (M.θL + M.ebar) = α * M.Θ - M.k := by
  unfold customerPayoff engageCost Params.Θ
  rw [effort_true]
  have h1 : M.θH + M.ebar - (M.θL + M.ebar) = M.θH - M.θL := by ring
  have h2 : 0 ≤ M.θH - M.θL := by linarith [M.θL_lt_θH]
  have h3 : M.θL + M.ebar - (M.θL + M.ebar) = 0 := by ring
  have h4 : (if true = true then M.k else 0) = M.k := rfl
  rw [h1, max_eq_left h2, h3, max_self, h4]
  ring

lemma cust_true_H (M : Params) (α : ℝ) :
    customerPayoff M α true (M.θH + M.ebar) = -M.k := by
  unfold customerPayoff engageCost
  rw [effort_true]
  have h1 : M.θH + M.ebar - (M.θH + M.ebar) = 0 := by ring
  have h2 : M.θL + M.ebar - (M.θH + M.ebar) ≤ 0 := by linarith [M.θL_lt_θH]
  have h4 : (if true = true then M.k else 0) = M.k := rfl
  rw [h1, max_self, max_eq_right h2, h4]
  ring

lemma cust_false_nonneg (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hbr : SequentialGame.IsBR0 (subgame M α).payoff0 false p) :
    0 ≤ customerPayoff M α false p := by
  rw [br_iff M α hα false, alpha_effort_false, effort_false, add_zero, add_zero] at hbr
  have hΘ := Θ_pos M
  rcases hbr with ⟨_, hp⟩ | ⟨_, hp⟩ | ⟨_, hp | hp⟩ <;> subst hp
  · rw [cust_false_L]; exact mul_nonneg hα.1 hΘ.le
  · rw [cust_false_H]
  · rw [cust_false_L]; exact mul_nonneg hα.1 hΘ.le
  · rw [cust_false_H]

lemma spne_true_imp_interval (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    {P : Bool → ℝ} (hsp : (subgame M α).IsSPNE true P) :
    M.m ≤ α ∧ α ≤ M.αbar := by
  have hbrF := hsp.1 false
  have hbrT := hsp.1 true
  have hopt : customerPayoff M α false (P false) ≤ customerPayoff M α true (P true) := hsp.2 false
  have hF0 : 0 ≤ customerPayoff M α false (P false) := cust_false_nonneg M α hα hbrF
  have hbrT_cases := (br_iff M α hα true (P true)).mp hbrT
  rw [alpha_effort_true, effort_true] at hbrT_cases
  have hPT : P true = M.θL + M.ebar ∧ α ≤ M.αbar := by
    rcases hbrT_cases with ⟨hlt, hp⟩ | ⟨_, hp⟩ | ⟨heq, hp | hp⟩
    · exact ⟨hp, hlt.le⟩
    · exfalso; rw [hp, cust_true_H] at hopt; linarith [M.k_pos]
    · exact ⟨hp, heq.le⟩
    · exfalso; rw [hp, cust_true_H] at hopt; linarith [M.k_pos]
  have hUT : customerPayoff M α true (P true) = α * M.Θ - M.k := by
    rw [hPT.1, cust_true_L]
  have hα1 : M.α₁ ≤ α := by
    unfold Params.α₁
    rw [div_le_iff₀ (Θ_pos M)]
    linarith
  have hα0 : M.α₀ ≤ α := by
    by_contra hlt
    have hlt' : α < M.α₀ := lt_of_not_ge hlt
    have hbrF_cases := (br_iff M α hα false (P false)).mp hbrF
    rw [alpha_effort_false, effort_false, add_zero, add_zero] at hbrF_cases
    have hpF : P false = M.θL := by
      rcases hbrF_cases with ⟨_, hp⟩ | ⟨hgt, _⟩ | ⟨heq, _⟩
      · exact hp
      · exfalso; exact not_lt_of_gt hlt' hgt
      · exfalso; exact ne_of_lt hlt' heq
    rw [hpF, cust_false_L, hUT] at hopt
    linarith [M.k_pos]
  exact ⟨max_le hα0 hα1, hPT.2⟩

noncomputable def P_eng (M : Params) : Bool → ℝ :=
  fun b => if b then M.θL + M.ebar else M.θH

lemma isSPNE_P_eng (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hm : M.m ≤ α ∧ α ≤ M.αbar) :
    (subgame M α).IsSPNE true (P_eng M) := by
  have hα0 : M.α₀ ≤ α := le_trans (le_max_left _ _) hm.1
  have hα1 : M.α₁ ≤ α := le_trans (le_max_right _ _) hm.1
  refine ⟨fun b => ?_, fun b => ?_⟩
  · cases b
    · have hbr := br_high_of_ge M α hα false (by rw [alpha_effort_false]; exact hα0)
      rw [effort_false, add_zero] at hbr
      exact hbr
    · have hbr := br_low_of_le M α hα true (by rw [alpha_effort_true]; exact hm.2)
      rw [effort_true] at hbr
      exact hbr
  · cases b
    · dsimp [subgame, P_eng]
      rw [cust_false_H, cust_true_L]
      unfold Params.α₁ at hα1
      have hk := (div_le_iff₀ (Θ_pos M)).mp hα1
      linarith
    · exact le_rfl

noncomputable def P_no (M : Params) (α : ℝ) : Bool → ℝ :=
  fun b =>
    if b then (if α < M.αbar then M.θL + M.ebar else M.θH + M.ebar)
    else (if α ≤ M.α₀ then M.θL else M.θH)

lemma isSPNE_P_no (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hnot : ¬ (M.m ≤ α ∧ α ≤ M.αbar)) :
    (subgame M α).IsSPNE false (P_no M α) := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · cases b
    · change SequentialGame.IsBR0 (subgame M α).payoff0 false
        (if α ≤ M.α₀ then M.θL else M.θH)
      split_ifs with hle
      · have hbr := br_low_of_le M α hα false (by rw [alpha_effort_false]; exact hle)
        rw [effort_false, add_zero] at hbr
        exact hbr
      · have hgt : M.α₀ ≤ α := (lt_of_not_ge hle).le
        have hbr := br_high_of_ge M α hα false (by rw [alpha_effort_false]; exact hgt)
        rw [effort_false, add_zero] at hbr
        exact hbr
    · change SequentialGame.IsBR0 (subgame M α).payoff0 true
        (if α < M.αbar then M.θL + M.ebar else M.θH + M.ebar)
      split_ifs with hlt
      · have hbr := br_low_of_le M α hα true (by rw [alpha_effort_true]; exact hlt.le)
        rw [effort_true] at hbr
        exact hbr
      · have hge : M.αbar ≤ α := le_of_not_gt hlt
        have hbr := br_high_of_ge M α hα true (by rw [alpha_effort_true]; exact hge)
        rw [effort_true] at hbr
        exact hbr
  · cases b
    · exact le_rfl
    · dsimp [subgame, P_no]
      split_ifs with hlt hle
      · rw [cust_true_L, cust_false_L]
        linarith [M.k_pos]
      · rw [cust_true_L, cust_false_H]
        have hgt0 : M.α₀ < α := lt_of_not_ge hle
        have hlt_m : α < M.m := by
          by_contra hge
          exact hnot ⟨le_of_not_gt hge, hlt.le⟩
        have hlt_α1 : α < M.α₁ := by
          rcases lt_max_iff.mp hlt_m with h0 | h1
          · exfalso; linarith
          · exact h1
        unfold Params.α₁ at hlt_α1
        have hk := (lt_div_iff₀ (Θ_pos M)).mp hlt_α1
        linarith
      · rw [cust_true_H, cust_false_L]
        have := mul_nonneg hα.1 (Θ_pos M).le
        linarith [M.k_pos]
      · rw [cust_true_H, cust_false_H]
        linarith [M.k_pos]

end Aux_EngageInfo_lemma_1

open EngageInfo CollabProject.TimeDep Aux_EngageInfo_lemma_1

theorem solution (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (∃ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P) ∧
    (M.m ≤ α ∧ α ≤ M.αbar →
      (∃ P : Bool → ℝ, (subgame M α).IsSPNE true P) ∧
      ∀ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P →
        sellerProfit M α (effort M b) (P b) = vstar M α → b = true) ∧
    (¬ (M.m ≤ α ∧ α ≤ M.αbar) →
      ∀ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P → b = false) := by
  have hexists : ∃ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P := by
    by_cases hm : M.m ≤ α ∧ α ≤ M.αbar
    · exact ⟨true, P_eng M, isSPNE_P_eng M α hα hm⟩
    · exact ⟨false, P_no M α, isSPNE_P_no M α hα hm⟩
  refine ⟨hexists, fun hm => ⟨⟨P_eng M, isSPNE_P_eng M α hα hm⟩, ?_⟩, fun hnot b P hsp => ?_⟩
  · intro b P hsp heq
    have hα0 : M.α₀ ≤ α := le_trans (le_max_left _ _) hm.1
    have hαpos : 0 < α := lt_of_lt_of_le (α₀_pos M) hα0
    have hHbar_pos : 0 < M.θH + M.ebar - M.c := by
      linarith [M.c_lt_θL, M.θL_lt_θH, ebar_pos M]
    have hbar_le : α * (M.θH + M.ebar - M.c) ≤ M.θL + M.ebar - M.c := by
      have h := hm.2
      unfold Params.αbar Params.alpha at h
      exact (le_div_iff₀ hHbar_pos).mp h
    have h0_ge : M.θL - M.c ≤ α * (M.θH - M.c) := by
      have h := hα0
      unfold Params.α₀ Params.alpha at h
      simp only [add_zero] at h
      exact (div_le_iff₀ (by linarith [M.c_lt_θL, M.θL_lt_θH])).mp h
    have hstrict : α * (M.θH - M.c) < M.θL + M.ebar - M.c := by
      have hmul : α * (M.θH - M.c) < α * (M.θH + M.ebar - M.c) :=
        mul_lt_mul_of_pos_left (by linarith [ebar_pos M]) hαpos
      linarith
    have hgreat : IsGreatest (spePayoffs M α) (M.θL + M.ebar - M.c) := by
      refine ⟨⟨true, P_eng M, isSPNE_P_eng M α hα hm, ?_⟩, ?_⟩
      · have hprof := br_profit_eq M α hα true ((isSPNE_P_eng M α hα hm).1 true)
        rw [effort_true, max_eq_left hbar_le] at hprof
        rw [effort_true]
        exact hprof.symm
      · rintro x ⟨b', P', hsp', rfl⟩
        have hprof := br_profit_eq M α hα b' (hsp'.1 b')
        cases b'
        · rw [effort_false, add_zero, add_zero, max_eq_right h0_ge] at hprof
          rw [effort_false, hprof]
          linarith
        · rw [effort_true, max_eq_left hbar_le] at hprof
          rw [effort_true, hprof]
    have hvstar : vstar M α = M.θL + M.ebar - M.c := hgreat.csSup_eq
    cases b
    · exfalso
      have hprof := br_profit_eq M α hα false (hsp.1 false)
      rw [effort_false, add_zero, add_zero, max_eq_right h0_ge] at hprof
      rw [effort_false] at heq
      linarith
    · rfl
  · cases b
    · rfl
    · exfalso
      exact hnot (spne_true_imp_interval M α hα hsp)
