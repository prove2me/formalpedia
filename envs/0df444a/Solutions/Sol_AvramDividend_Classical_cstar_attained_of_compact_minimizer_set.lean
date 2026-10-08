-- Prove2me | solution 1 for AvramDividend.Classical.cstar_attained_of_compact_minimizer_set
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:15:32.017982+00:00
-- url     : https://prove2.me/submissions/1a49a9bc-9cd4-46d9-a1f2-b976af374cb4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hcompact : IsCompact (cstarSet W))
    (hnonempty : (cstarSet W).Nonempty) :
    (cstar W).toReal ∈ cstarSet W := by
  obtain ⟨a, ha⟩ := hnonempty
  have hcompact' : IsCompact (cstarSet W ∩ Set.Icc 0 a) :=
    hcompact.inter_right isClosed_Icc
  exact cstar_attained_of_compact_initial_minimizers W a ha hcompact'
