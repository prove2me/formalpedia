-- Prove2me | solution 1 for ComparativeAdvantage.comparative_advantage_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:39:31.728414+00:00
-- url     : https://prove2.me/submissions/d72054a8-261c-440a-9bc6-ce9717da2fb6

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution (h f : Country) :
    h.aLC / f.aLC < h.aLW / f.aLW ↔
      HasComparativeAdvantageInCloth h f := by
  change h.aLC / f.aLC < h.aLW / f.aLW ↔
    h.aLC / h.aLW < f.aLC / f.aLW
  rw [div_lt_div_iff₀ f.aLC_pos f.aLW_pos,
      div_lt_div_iff₀ h.aLW_pos f.aLW_pos]
  constructor <;> intro hlt <;> nlinarith
