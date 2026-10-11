-- Prove2me | solution 1 for ComparativeAdvantage.trade_frontier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:46:53.193251+00:00
-- url     : https://prove2.me/submissions/3b5745ee-e46d-4065-b406-af5a9c0028c0

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution (c : Country) (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW)
    (hp : c.aLC / c.aLW ≤ PC / PW) :
    (∀ q : ℝ × ℝ, q ∈ tradeSetCloth c PC PW ↔
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 ≤ c.L / c.aLC - (PW / PC) * q.2) ∧
    ∀ QW : ℝ, 0 ≤ QW →
      c.L / c.aLC - (c.aLW / c.aLC) * QW ≤
        c.L / c.aLC - (PW / PC) * QW := by
  constructor
  · intro q
    constructor
    · intro hq
      rcases hq with ⟨hx, hy, hbudget⟩
      refine ⟨hx, hy, ?_⟩
      apply le_sub_iff_add_le.mpr
      apply (le_div_iff₀ c.aLC_pos).2
      have heq :
          (q.1 + PW / PC * q.2) * c.aLC =
            c.aLC * q.1 + c.aLC * (PW / PC) * q.2 := by ring
      rw [heq]
      exact hbudget
    · rintro ⟨hx, hy, hbudget⟩
      refine ⟨hx, hy, ?_⟩
      have hh := (le_div_iff₀ c.aLC_pos).1
        (le_sub_iff_add_le.mp hbudget)
      have heq :
          (q.1 + PW / PC * q.2) * c.aLC =
            c.aLC * q.1 + c.aLC * (PW / PC) * q.2 := by ring
      rwa [heq] at hh
  · intro QW hQW
    have hcross : c.aLC * PW ≤ PC * c.aLW :=
      (div_le_div_iff₀ c.aLW_pos hPW).1 hp
    have hratio : PW / PC ≤ c.aLW / c.aLC :=
      (div_le_div_iff₀ hPC c.aLC_pos).2 (by nlinarith)
    have hm := mul_le_mul_of_nonneg_right hratio hQW
    linarith
