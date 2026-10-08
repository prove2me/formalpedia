-- Prove2me | solution 1 for AvramDividend.Classical.cstar_attained_of_compact_initial_minimizers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:42:46.21225+00:00
-- url     : https://prove2.me/submissions/2383b2ec-c63d-4206-91f8-8ef9b89a9b07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical
open scoped ENNReal

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hcompact : IsCompact (cstarSet W ∩ Set.Icc 0 a)) :
    (cstar W).toReal ∈ cstarSet W := by
  classical
  have hnonempty : (cstarSet W ∩ Set.Icc 0 a).Nonempty :=
    ⟨a, ha, ⟨ha.1.le, le_rfl⟩⟩
  obtain ⟨b, hb⟩ := hcompact.exists_isLeast hnonempty
  have hbmem : b ∈ cstarSet W := hb.1.1
  have hble : ∀ c ∈ cstarSet W, b ≤ c := by
    intro c hc
    by_cases hca : c ≤ a
    · exact hb.2 ⟨hc, ⟨hc.1.le, hca⟩⟩
    · exact hb.1.2.2.trans (le_of_not_ge hca)
  have hdef : cstar W = ENNReal.ofReal b := by
    unfold cstar
    rw [if_pos ⟨b, hbmem⟩]
    apply le_antisymm
    · exact iInf_le_of_le b (iInf_le _ hbmem)
    · apply le_iInf
      intro c
      apply le_iInf
      intro hc
      exact ENNReal.ofReal_le_ofReal (hble c hc)
  rw [hdef, ENNReal.toReal_ofReal hbmem.1.le]
  exact hbmem
