-- Prove2me | solution 1 for ComparativeAdvantage.relative_price_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:48:09.733986+00:00
-- url     : https://prove2.me/submissions/bfc11ac0-5989-4f5f-8051-7b6b639bb64c

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution (h f : Country) (hCA : HasComparativeAdvantageInCloth h f)
    (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW) (qH qF : ℝ × ℝ)
    (hqH : IsCompetitiveOutput h PC PW qH) (hqF : IsCompetitiveOutput f PC PW qF)
    (hcloth : 0 < qH.1 + qF.1) (hwine : 0 < qH.2 + qF.2) :
    h.aLC / h.aLW ≤ PC / PW ∧ PC / PW ≤ f.aLC / f.aLW := by
  change h.aLC / h.aLW < f.aLC / f.aLW at hCA
  have cloth_wage (c : Country) (hw : PW / c.aLW ≤ PC / c.aLC) :
      c.aLC / c.aLW ≤ PC / PW := by
    have hc : PW * c.aLC ≤ PC * c.aLW :=
      (div_le_div_iff₀ c.aLW_pos c.aLC_pos).1 hw
    exact (div_le_div_iff₀ c.aLW_pos hPW).2 (by nlinarith)
  have wine_wage (c : Country) (hw : PC / c.aLC ≤ PW / c.aLW) :
      PC / PW ≤ c.aLC / c.aLW := by
    have hc : PC * c.aLW ≤ PW * c.aLC :=
      (div_le_div_iff₀ c.aLC_pos c.aLW_pos).1 hw
    exact (div_le_div_iff₀ hPW c.aLW_pos).2 (by nlinarith)
  rcases hqH with ⟨hHc, hHw, hHl, hHwageC, hHwageW⟩
  rcases hqF with ⟨hFc, hFw, hFl, hFwageC, hFwageW⟩
  constructor
  · by_cases hh : 0 < qH.1
    · exact cloth_wage h (hHwageC hh)
    · have hf : 0 < qF.1 := by nlinarith
      exact le_trans (le_of_lt hCA) (cloth_wage f (hFwageC hf))
  · by_cases hf : 0 < qF.2
    · exact wine_wage f (hFwageW hf)
    · have hh : 0 < qH.2 := by nlinarith
      exact le_trans (wine_wage h (hHwageW hh)) (le_of_lt hCA)
