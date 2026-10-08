-- Prove2me | solution 1 for AvramDividend.Classical.cstar_attained_of_right_deriv_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:38:23.376291+00:00
-- url     : https://prove2.me/submissions/f1422d28-3e1a-4b02-84fb-c7d0b605f4f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_right_deriv_gap
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    (cstar W).toReal ∈ cstarSet W := by
  have hclosed : IsClosed (cstarSet W) :=
    cstarSet_closed_of_right_deriv_gap W a ha hgap hcont
  have hcompact : IsCompact (cstarSet W ∩ Set.Icc 0 a) :=
    isCompact_Icc.of_isClosed_subset
      (hclosed.inter isClosed_Icc) Set.inter_subset_right
  exact cstar_attained_of_compact_initial_minimizers W a ha hcompact
