-- Prove2me | solution 1 for ComparativeAdvantage.gains_from_trade
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:52:41.372521+00:00
-- url     : https://prove2.me/submissions/f078252b-af78-4dba-95f8-7818cd847d95

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

private theorem budget_strict_second (a b k L : ℝ)
    (hb : 0 < b) (hk : 0 < k) (hL : 0 < L) (hkb : k < b) :
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ a * q.1 + b * q.2 ≤ L} ⊂
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ a * q.1 + k * q.2 ≤ L} := by
  refine ssubset_iff_subset_not_subset.mpr ⟨?_, ?_⟩
  · intro q hq
    rcases hq with ⟨hx, hy, hbudget⟩
    have hm := mul_le_mul_of_nonneg_right (le_of_lt hkb) hy
    exact ⟨hx, hy, by nlinarith⟩
  · intro hback
    let y : ℝ := L / k
    have hy : 0 < y := div_pos hL hk
    have heq : k * y = L := by
      dsimp [y]
      field_simp [ne_of_gt hk]
    have ht : ((0 : ℝ), y) ∈
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ a * q.1 + k * q.2 ≤ L} := by
      exact ⟨by norm_num, le_of_lt hy, by dsimp; nlinarith⟩
    rcases hback ht with ⟨_, _, hbgt⟩
    have hm := mul_lt_mul_of_pos_right hkb hy
    dsimp at hbgt
    nlinarith

private theorem budget_strict_first (a b k L : ℝ)
    (ha : 0 < a) (hk : 0 < k) (hL : 0 < L) (hka : k < a) :
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ a * q.1 + b * q.2 ≤ L} ⊂
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ k * q.1 + b * q.2 ≤ L} := by
  refine ssubset_iff_subset_not_subset.mpr ⟨?_, ?_⟩
  · intro q hq
    rcases hq with ⟨hx, hy, hbudget⟩
    have hm := mul_le_mul_of_nonneg_right (le_of_lt hka) hx
    exact ⟨hx, hy, by nlinarith⟩
  · intro hback
    let x : ℝ := L / k
    have hx : 0 < x := div_pos hL hk
    have heq : k * x = L := by
      dsimp [x]
      field_simp [ne_of_gt hk]
    have ht : (x, (0 : ℝ)) ∈
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ k * q.1 + b * q.2 ≤ L} := by
      exact ⟨le_of_lt hx, by norm_num, by dsimp; nlinarith⟩
    rcases hback ht with ⟨_, _, hbgt⟩
    have hm := mul_lt_mul_of_pos_right hka hx
    dsimp at hbgt
    nlinarith

theorem solution (h f : Country) (hCA : HasComparativeAdvantageInCloth h f)
    (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW)
    (hlow : h.aLC / h.aLW ≤ PC / PW)
    (hhigh : PC / PW ≤ f.aLC / f.aLW) :
    autarkySet h ⊆ tradeSetCloth h PC PW ∧
    autarkySet f ⊆ tradeSetWine f PC PW ∧
    (h.aLC / h.aLW < PC / PW → autarkySet h ⊂ tradeSetCloth h PC PW) ∧
    (PC / PW < f.aLC / f.aLW → autarkySet f ⊂ tradeSetWine f PC PW) := by
  have hHcross : h.aLC * PW ≤ PC * h.aLW :=
    (div_le_div_iff₀ h.aLW_pos hPW).1 hlow
  have hFcross : PC * f.aLW ≤ f.aLC * PW :=
    (div_le_div_iff₀ hPW f.aLW_pos).1 hhigh
  have hHcoeff : h.aLC * (PW / PC) ≤ h.aLW := by
    calc
      h.aLC * (PW / PC) = (h.aLC * PW) / PC := by ring
      _ ≤ h.aLW := (div_le_iff₀ hPC).2 (by nlinarith)
  have hFcoeff : f.aLW * (PC / PW) ≤ f.aLC := by
    calc
      f.aLW * (PC / PW) = (f.aLW * PC) / PW := by ring
      _ ≤ f.aLC := (div_le_iff₀ hPW).2 (by nlinarith)
  have hsubH : autarkySet h ⊆ tradeSetCloth h PC PW := by
    intro q hq
    rcases hq with ⟨hx, hy, hbudget⟩
    have hm := mul_le_mul_of_nonneg_right hHcoeff hy
    exact ⟨hx, hy, by nlinarith⟩
  have hsubF : autarkySet f ⊆ tradeSetWine f PC PW := by
    intro q hq
    rcases hq with ⟨hx, hy, hbudget⟩
    have hm := mul_le_mul_of_nonneg_right hFcoeff hx
    exact ⟨hx, hy, by nlinarith⟩
  refine ⟨hsubH, hsubF, ?_, ?_⟩
  · intro hstrict
    have hc : h.aLC * PW < PC * h.aLW :=
      (div_lt_div_iff₀ h.aLW_pos hPW).1 hstrict
    have hlt : h.aLC * (PW / PC) < h.aLW := by
      calc
        h.aLC * (PW / PC) = (h.aLC * PW) / PC := by ring
        _ < h.aLW := (div_lt_iff₀ hPC).2 (by nlinarith)
    exact budget_strict_second h.aLC h.aLW (h.aLC * (PW / PC)) h.L
      h.aLW_pos (mul_pos h.aLC_pos (div_pos hPW hPC)) h.L_pos hlt
  · intro hstrict
    have hc : PC * f.aLW < f.aLC * PW :=
      (div_lt_div_iff₀ hPW f.aLW_pos).1 hstrict
    have hlt : f.aLW * (PC / PW) < f.aLC := by
      calc
        f.aLW * (PC / PW) = (f.aLW * PC) / PW := by ring
        _ < f.aLC := (div_lt_iff₀ hPW).2 (by nlinarith)
    exact budget_strict_first f.aLC f.aLW (f.aLW * (PC / PW)) f.L
      f.aLC_pos (mul_pos f.aLW_pos (div_pos hPC hPW)) f.L_pos hlt
