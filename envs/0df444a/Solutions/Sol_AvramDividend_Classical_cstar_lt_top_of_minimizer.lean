-- Prove2me | solution 1 for AvramDividend.Classical.cstar_lt_top_of_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T13:36:44.684764+00:00
-- url     : https://prove2.me/submissions/0fb2f3c0-5e5f-4ccf-8cd1-83db87a2be6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical
open scoped ENNReal

theorem solution
    (W : ℝ → ℝ) (hmin : (cstarSet W).Nonempty) :
    cstar W < ⊤ := by
  classical
  obtain ⟨a, ha⟩ := hmin
  have hmin' : (cstarSet W).Nonempty := ⟨a, ha⟩
  have hle : cstar W ≤ ENNReal.ofReal a := by
    unfold cstar
    rw [if_pos hmin']
    exact iInf_le_of_le a (iInf_le _ ha)
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
